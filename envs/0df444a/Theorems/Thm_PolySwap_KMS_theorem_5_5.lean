-- Prove2me | Theorems.Thm_PolySwap_KMS_theorem_5_5
-- name    : PolySwap.KMS.theorem_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:41:42.13316+00:00
-- url     : https://prove2.me/theorems/25c4734f-ae81-4d6b-835c-6fc98bc891cd
-- title:
--   Theorem 5.5 — $\mathrm{Unip}_n(R)=\langle S_{\mathrm{Elm}}\mid R_{\mathrm{Elm}}\rangle$ with $\mathrm{Dehn}(m)\le C'm$, $C'$ independent of $n$ and $R$
-- statement:
--   For every commutative unital ring $R$ and every $n\ge5$, the group $\mathrm{Unip}_n(R)$ is presented as $\langle S_{\mathrm{Elm}}\mid R_{\mathrm{Elm}}\rangle$. Moreover there is a universal constant $C'$, independent of $n$ and $R$, such that for every $m$
--   $$\mathrm{Dehn}_{S_{\mathrm{Elm}},R_{\mathrm{Elm}}}(m)\le C'm.$$
--
--   Differences from the source:
--   - reading: (Elm2): [E_{i,j}(A₁), E_{k,l}(A₂)] = E_{i,k}(A₁A₂) if j = k → RElm uses E_{i,l}(A₁A₂) when j = k; reason: obvious typo: for j = k the commutator of block elementary matrices is E_{i,l}(A₁A₂) (block form of [e_{ij}(a), e_{jl}(b)] = e_{il}(ab)); as printed the relation is false in Unip_n(R) and no presentation could hold (INSIGHTS I3)
--   - encoding: (i, j)-admissible block matrices A of sizes k₀ × k₀, k₀ × k₁, k₁ × k₀ and E_{i,j}(A) → n × n matrices: A embedded in block position (i, j) for i < j with E = 1 + A; the full matrix E_{i,i}(A) for i = j; reason: block sums, products and inverses become the n × n operations; the same generators and relations
--   - encoding: Unip_n(R), the group of upper unitriangular matrices; S_Elm a set of matrices; R_Elm equations between words → Unip n R as a subgroup of SL (Fin n) R; SElm n R ⊆ Unip n R; each relation a word in FreeGroup (SElm n R) equal to 1 (x y z⁻¹ for xy = z); reason: upper unitriangular matrices have determinant 1; standard encoding of relations
--   - encoding: the universal constant C′ (a real number), R any commutative unital ring → ∃ C′ : ℕ before n and R : Type u (one universe level); reason: Dehn values are integers, so a real C′ can be replaced by ⌈C′⌉; Lean quantifies over the rings of one universe
--   - encoding: Dehn functions, areas, radii and diameters with values in ℕ (a max over a finite set) → values in ℕ∞ (iSup/iInf; ⊤ when there is no filling or path); reason: no junk value 0 for an empty or unbounded set; equal to the paper's value whenever that is finite
--   - encoding: n ≥ 5 (the 5-block form is defined assuming n ≥ 5, p. 37) → hypothesis 5 ≤ n; reason: the section's standing assumption
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Theorem 5.5, p. 39 (presentation defined p. 38; n ≥ 5 from the 5-block form, p. 37)

import Mathlib
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_Unip

universe u

namespace PolySwap.KMS

/-- **Theorem 5.5**, p. 39. For every commutative unital ring `R` and every `n ≥ 5`, the group
`Unip_n(R)` is presented as `⟨S_Elm | R_Elm⟩`. Moreover there is a universal constant `C'`,
independent of `n` and `R`, with `Dehn_{S_Elm,R_Elm}(m) ≤ C' m` for every `m`. -/
theorem theorem_5_5 :
    (∀ (n : ℕ) (R : Type u) [CommRing R], 5 ≤ n → IsPresentation (sElmIncl n R) (RElm n R)) ∧
    ∃ C' : ℕ, ∀ (n : ℕ) (R : Type u) [CommRing R], 5 ≤ n →
      ∀ m : ℕ, dehn (sElmIncl n R) (RElm n R) m ≤ (C' : ℕ∞) * m := by sorry

end PolySwap.KMS
