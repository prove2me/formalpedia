-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_finitelyGeneratedDual
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.finitelyGeneratedDual
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:22:31.881181+00:00
-- url     : https://prove2.me/theorems/28901917-aebc-44cf-96ac-91d29a49aedf
-- title:
--   A fixed locality suffices when the continuous character group is finitely generated
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   For topological assertions, assume that the on-site characters are continuous. A finite group has its usual discrete topology; a compact Lie group is finite dimensional, real and Hausdorff.
--
--   Assume $G$ finite or compact Lie and its Pontryagin dual $\widehat G=\operatorname{Hom}_{\mathrm{continuous}}(G,U(1))$ is finitely generated as an abstract group. For the fixed on-site representation there is an integer $K\ge2$, independent of system size, such that
--
--   $$
--   \forall n\ge1,\qquad
--   \bigoplus_\mu SU(\mathcal H_\mu^{(n)})\subseteq\mathcal V_{n,\min(K,n)}.
--   $$
--
--   Here finite generation means that some finite set of continuous characters generates the whole dual group algebraically. For $n<K$, capping locality at $n$ permits all system sites.
--
--   This is the source's fixed-locality existence assertion; no effective numerical $K$ or proof is supplied on p.10.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 10, VII, unnumbered: a fixed locality suffices for finitely generated dual

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF p.10 VII: finite generation of the actual continuous character group gives one
finite locality bound, chosen before system size. For n < K, locality is capped at n. -/
theorem finitelyGeneratedDual [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [Nonempty A] (chi : A → G → ℂ) (hchi : IsOnsite chi)
    (hcont : ∀ a, Continuous (chi a)) (hreg : Finite G ∨ CompactLie G)
    (hdual : ∃ S : Finset (G →ₜ* Circle),
      Subgroup.closure (S : Set (G →ₜ* Circle)) = ⊤) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → SemiUniversal chi n (min K n) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
