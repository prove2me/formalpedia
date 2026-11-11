-- Prove2me | Theorems.Thm_PolySwap_KMS_theorem_3_19
-- name    : PolySwap.KMS.theorem_3_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:40:48.597196+00:00
-- url     : https://prove2.me/theorems/adbed239-71b9-461c-a280-db2ec473d570
-- title:
--   Theorem 3.19 (= Theorem B.7, first part) — a 1-connected coset complex has a 1-cone with $\mathrm{Rad}_0\le D$, $\mathrm{Rad}_1\le15(\mathrm{Dehn}_Y(2D+1)+2D+1)$
-- statement:
--   Let $G$ be a finite group with subgroups $H_i$, $i\in I$, where $|I|\ge3$, and assume the coset complex $Y=CC(G;(H_i)_{i\in I})$ is 1-connected. Let $\mathrm{Dehn}_Y$ be as in Definition 2.35 and $D=\mathrm{diam}(Y)$. Then $Y$ admits a 1-cone $\mathrm{Cone}_Y$ with
--   $$\mathrm{Rad}_0(\mathrm{Cone}_Y)\le D,\qquad\mathrm{Rad}_1(\mathrm{Cone}_Y)\le15\big(\mathrm{Dehn}_Y(2D+1)+2D+1\big).$$
--   The same statement is the first implication of Theorem B.7, p. 63.
--
--   Differences from the source:
--   - encoding: D = diam(Y) → a natural number D with hypothesis (cosetComplex G H).diam = D; reason: a 1-connected finite complex has finite diameter, so this covers every case
--   - encoding: 1-connected: the geometric realization |Y| is path-connected and simply connected (Definition 2.28) → IsOneConnected: connected, and every edge loop is reduced to the trivial loop by (BT)/(TR) moves; reason: Remark 2.29 / the edge-path group theorem: the two notions coincide
--   - encoding: the coset complex CC(G; (H_i)) with vertex set ⊔_i G/H_i (Definition 2.4) → cosetComplex G H : WComplex (Σ i, G ⧸ H i), maximal faces the chambers {gH_i : i}, uniform top weight; reason: Lean convention for ⊔_i G/H_i; same faces and weights
--   - reading: Definition 2.35: generators 'all the elements of the H_i', relations R_i 'all the nontrivial relations in the multiplication table of H_i of length at most 3' (Appendix B, p. 61, writes S = ⋃H_i ∖ {1}) → cosetDehn: letters = the elements of ⋃_i H_i ∖ {1}; R_i = the positive words [a][b], [a][b][c] with letters in H_i ∖ {1} whose product is 1; reason: Appendix B (pp. 61–62), where Theorem 3.19 is proved, fixes S = ⋃H_i ∖ {1} and uses exactly the relations [g][g⁻¹] = 1 and the three-letter triangle words
--   - encoding: Dehn functions, areas, radii and diameters with values in ℕ (a max over a finite set) → values in ℕ∞ (iSup/iInf; ⊤ when there is no filling or path); reason: no junk value 0 for an empty or unbounded set; equal to the paper's value whenever that is finite
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Theorem 3.19, p. 28 (= Theorem B.7, first implication, p. 63; proof pp. 57–63)

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Cone
import Definitions.Def_PolySwap_KMS_Dehn

namespace PolySwap.KMS

/-- **Theorem 3.19** (= Theorem B.7, first implication, p. 63), p. 28. Let `G` be a finite group
with subgroups `H_i`, `i ∈ I`, `|I| ≥ 3`, such that `Y = CC(G; (H_i))` is 1-connected, and let
`D = diam(Y)`. Then `Y` admits a 1-cone with `Rad₀ ≤ D` and
`Rad₁ ≤ 15(Dehn_Y(2D + 1) + 2D + 1)`. -/
theorem theorem_3_19 {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι]
    (hι : 3 ≤ Fintype.card ι) (H : ι → Subgroup G)
    (hY : (cosetComplex G H).IsOneConnected) (D : ℕ) (hD : (cosetComplex G H).diam = D) :
    ∃ C : WComplex.OneCone (Σ i, G ⧸ H i), (cosetComplex G H).IsOneCone C ∧
      (cosetComplex G H).rad0 C ≤ D ∧
      (cosetComplex G H).rad1 C ≤ 15 * (cosetDehn H (2 * D + 1) + ((2 * D + 1 : ℕ) : ℕ∞)) := by sorry

end PolySwap.KMS
