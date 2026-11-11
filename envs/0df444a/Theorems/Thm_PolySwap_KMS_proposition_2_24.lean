-- Prove2me | Theorems.Thm_PolySwap_KMS_proposition_2_24
-- name    : PolySwap.KMS.proposition_2_24
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:40:38.405171+00:00
-- url     : https://prove2.me/theorems/f46a90a0-7472-497b-9364-35d964ac182b
-- title:
--   Proposition 2.24 — change of presentation: $\mathrm{Dehn}_{S,R}(m)\le C_2\,\mathrm{Dehn}_{S',R'}(C_1m)+C_3m$
-- statement:
--   Let $G$ be a group with two finite presentations $G=\langle S\mid R\rangle=\langle S'\mid R'\rangle$ ($S,S'$ finite symmetric generating sets, $R,R'$ finite). Choose $\phi:\mathrm{Free}(S)\to\mathrm{Free}(S')$ sending each $s\in S$ to a word $w_s$ with $s=w_s$ in $G$ and $|w_s|_{S'}$ minimal, and $\phi':\mathrm{Free}(S')\to\mathrm{Free}(S)$ likewise. Put $C_1=\max_{s\in S}|\phi(s)|_{S'}$, $C_2=\max_{\rho'\in R'}\mathrm{Area}_R(\phi'(\rho'))$ and $C_3=\max_{s\in S}\mathrm{Area}_R\big(s\,(\phi'(\phi(s)))^{-1}\big)$. Then for every $m\in\mathbb N$
--   $$\mathrm{Dehn}_{S,R}(m)\le C_2\,\mathrm{Dehn}_{S',R'}(C_1m)+C_3m.$$
--
--   Differences from the source:
--   - encoding: the maxima C₁, C₂, C₃ and the Dehn functions in ℕ → C₁ = ⨆ s, wordLength (φ s) in ℕ (S finite); C₂, C₃ and the Dehn functions in ℕ∞ via iSup; reason: finite maxima; every area involved is finite because both are presentations, so no ⊤ or 0·⊤ occurs
--   - encoding: for every m ∈ ℕ (ℕ positive) → ∀ m : ℕ, including m = 0; reason: at m = 0 both sides are trivially 0 ≤ …; no instance changes
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Proposition 2.24, p. 17

import Mathlib
import Definitions.Def_PolySwap_KMS_Dehn

namespace PolySwap.KMS

/-- **Proposition 2.24** (change of presentation), p. 17. Let `G = ⟨S | R⟩ = ⟨S' | R'⟩` be two
finite presentations (§2.5: `S`, `S'` finite symmetric generating sets, `R`, `R'` finite). Let
`ϕ : Free(S) → Free(S')` send every `s ∈ S` to a shortest word `ϕ(s)` in `S'` equal to `s` in `G`,
and `ϕ' : Free(S') → Free(S)` likewise. With `C₁ = max_s |ϕ(s)|_{S'}`,
`C₂ = max_{ρ' ∈ R'} Area_R(ϕ'(ρ'))` and `C₃ = max_s Area_R(s (ϕ'(ϕ(s)))⁻¹)`, for every `m`,
`Dehn_{S,R}(m) ≤ C₂ · Dehn_{S',R'}(C₁ m) + C₃ m`. -/
theorem proposition_2_24 {G : Type*} [Group G] {S S' : Type*} [Finite S] [Finite S']
    (ι : S → G) (R : Set (FreeGroup S)) (ι' : S' → G) (R' : Set (FreeGroup S'))
    (hP : IsPresentation ι R) (hP' : IsPresentation ι' R') (hR : R.Finite) (hR' : R'.Finite)
    (hS : ∀ s, ∃ t, ι t = (ι s)⁻¹) (hS' : ∀ s', ∃ t', ι' t' = (ι' s')⁻¹)
    (φ : S → FreeGroup S') (φ' : S' → FreeGroup S)
    (hφ : ∀ s, FreeGroup.lift ι' (φ s) = ι s ∧
      ∀ w, FreeGroup.lift ι' w = ι s → wordLength (φ s) ≤ wordLength w)
    (hφ' : ∀ s', FreeGroup.lift ι (φ' s') = ι' s' ∧
      ∀ w, FreeGroup.lift ι w = ι' s' → wordLength (φ' s') ≤ wordLength w) :
    ∀ m : ℕ, dehn ι R m ≤
      (⨆ ρ' ∈ R', area R (FreeGroup.lift φ' ρ')) *
          dehn ι' R' ((⨆ s, wordLength (φ s)) * m) +
        (⨆ s, area R (FreeGroup.of s * (FreeGroup.lift φ' (φ s))⁻¹)) * (m : ℕ∞) := by sorry

end PolySwap.KMS
