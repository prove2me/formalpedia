-- Prove2me | Theorems.Thm_SunGroupIso_Class2_lemma_4_4
-- name    : SunGroupIso.Class2.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:06:55.645909+00:00
-- url     : https://prove2.me/theorems/2b702638-5408-467d-98c2-68be7a933a3e
-- title:
--   Lemma 4.4 — restriction isomorphism iff matched extensions of the decompositions
-- statement:
--   Let $(z,Y,g,F,\rho)$ and $(z',X,g',E,\rho')$ be group restrictions (same parameters) of finite class-2 $p$-groups $G$ and $H$, with $\mathrm{ord}(z_i)=\mathrm{ord}(z'_i)$ and $\mathrm{ord}(\tilde g_i)=\mathrm{ord}(\tilde g'_i)$ (standing assumptions of p. 13–14). There is a group restriction isomorphism from $G$ to $H$ if and only if there are $z_{\zeta+1},\dots,z_{\zeta+\psi}$, $z'_{\zeta+1},\dots,z'_{\zeta+\psi}$, $g_{\gamma+1},\dots,g_{\gamma+\eta}\in F$, $g'_{\gamma+1},\dots,g'_{\gamma+\eta}\in E$ ($\psi=\mathrm{rank}\,Y$, $\eta=\mathrm{rank}\,\langle F,Z(G)\rangle/Z(G)$) with: (1) $Y=\bigoplus\langle z_{\zeta+i}\rangle$, $X=\bigoplus\langle z'_{\zeta+i}\rangle$, equal orders; (2) $\langle F,Z(G)\rangle/Z(G)=\bigoplus\langle\tilde g_{\gamma+i}\rangle$, $\langle E,Z(H)\rangle/Z(H)=\bigoplus\langle\tilde g'_{\gamma+i}\rangle$, equal orders; (3) for every $i\in[\gamma+\eta]$ the coefficients of $g_i^{\mathrm{ord}(\tilde g_i)}$ on $z_1,\dots,z_{\zeta+\psi}$ equal those of $g_i'^{\mathrm{ord}(\tilde g'_i)}$ on $z'_1,\dots,z'_{\zeta+\psi}$; (4) the same for $[g_i,g_j]$ and $[g'_i,g'_j]$, all $i,j\in[\gamma+\eta]$; (5) $\rho(g_i)=\rho'(g'_i)$ for $\gamma<i\le\gamma+\eta$.
--
--   Differences from the source:
--   - reading: the standing assumptions 'we may assume' of pp. 13–14 (conditions 4 and 5: ord(z_i) = ord(z'_i), ord(g̃_i) = ord(g̃'_i)) → hypotheses hz, hg; reason: stated once before the lemma for the whole problem and used by its proof through Lemma 3.1 (FAITHFULNESS_TRAPS row 19); the other standing conditions (equal ψ, η; Y ≅ X; quotients isomorphic; equal α for i, j ≤ γ) follow from either side of the equivalence
--   - reading: two group restrictions (Problem 4.3) → two restrictions with the same parameters ζ, γ, κ, τ, δ; reason: restriction isomorphism compares z_i with z'_i, g_i with g'_i and ρ with ρ' coordinatewise, and condition 1 of p. 13 assumes the parameters equal
--   - encoding: ρ : F → R^κ → ρ : G → Fin κ → ZMod (p^τ), only its values on F used by any condition or code; reason: a function on F is the restriction of a function on G; values off F are never read
--   - encoding: one-based indices → zero-based Fin indices (or the one-based helper at1); reason: a bijective reindexing
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 4.4, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_SunGroupIso_Class2_Restriction

set_option autoImplicit false

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)
open GroupIsoPoly (encPair cayley)

/-- **Lemma 4.4** (Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 4.4, p. 14, PDF p. 16). Let `(z, Y, g, F, ρ)` and `(z', X, g', E, ρ')`
be group restrictions of class-2 `p`-groups `G` and `H` (with the standing assumptions of p. 13–14
`ord(z_i) = ord(z'_i)`, `ord(g̃_i) = ord(g̃'_i)`). There is a group restriction isomorphism from `G` to `H`
if and only if there are `z_{ζ+1}, …, z_{ζ+ψ} ∈ Y`, `z'_{ζ+1}, …, z'_{ζ+ψ} ∈ X`,
`g_{γ+1}, …, g_{γ+η} ∈ F`, `g'_{γ+1}, …, g'_{γ+η} ∈ E` with: (1) `Y = ⊕⟨z_{ζ+i}⟩`, `X = ⊕⟨z'_{ζ+i}⟩`,
equal orders; (2) `⟨F,Z(G)⟩/Z(G) = ⊕⟨g̃_{γ+i}⟩`, `⟨E,Z(H)⟩/Z(H) = ⊕⟨g̃'_{γ+i}⟩`, equal orders; (3) the
coefficients of `g_i^{ord(g̃_i)}` and `g'_i^{ord(g̃'_i)}` on `z_1, …, z_{ζ+ψ}` agree for `i ∈ [γ+η]`;
(4) those of `[g_i, g_j]` and `[g'_i, g'_j]` agree; (5) `ρ(g_i) = ρ'(g'_i)` for `γ < i ≤ γ+η`. -/
theorem lemma_4_4 {p : ℕ} (hp : p.Prime) {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (hG : IsPGroupClass2 p G) (hH : IsPGroupClass2 p H) {ζ γ κ τ δ : ℕ}
    (r : Restriction G p ζ γ κ τ) (r' : Restriction H p ζ γ κ τ)
    (hr : IsRestriction p δ r) (hr' : IsRestriction p δ r')
    (hz : ∀ i, orderOf (r.z i) = orderOf (r'.z i))
    (hg : ∀ i, orderOf (tl (r.g i)) = orderOf (tl (r'.g i))) :
    (∃ f : G ≃* H, IsRestrictionIso r r' f) ↔
      ∃ (zY : Fin r.psi → G) (zX : Fin r.psi → H) (gF : Fin r.eta → G) (gE : Fin r.eta → H),
        (∀ i, gF i ∈ r.F) ∧ (∀ i, gE i ∈ r'.F) ∧
        (DecompWith r.Y zY ⊥ ∧ DecompWith r'.Y zX ⊥ ∧ ∀ i, orderOf (zY i) = orderOf (zX i)) ∧
        (DecompWith r.Kq (fun i => tl (gF i)) ⊥ ∧ DecompWith r'.Kq (fun i => tl (gE i)) ⊥ ∧
          ∀ i, orderOf (tl (gF i)) = orderOf (tl (gE i))) ∧
        (∀ i : Fin (γ + r.eta),
          coeffsWith (Fin.append r.z zY) ⊥
              (Fin.append r.g gF i ^ orderOf (tl (Fin.append r.g gF i))) =
            coeffsWith (Fin.append r'.z zX) ⊥
              (Fin.append r'.g gE i ^ orderOf (tl (Fin.append r'.g gE i)))) ∧
        (∀ i j : Fin (γ + r.eta),
          coeffsWith (Fin.append r.z zY) ⊥ ⁅Fin.append r.g gF i, Fin.append r.g gF j⁆ =
            coeffsWith (Fin.append r'.z zX) ⊥ ⁅Fin.append r'.g gE i, Fin.append r'.g gE j⁆) ∧
        (∀ i, r.ρ (gF i) = r'.ρ (gE i)) := by sorry

end SunGroupIso.Class2
