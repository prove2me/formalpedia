-- Prove2me | Theorems.Thm_WeierstrassCurve_inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn
-- name    : WeierstrassCurve.inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/f010fe8f-eb37-51f3-aa6c-eddca5817a77
-- title:
--   Inertia displacements lie in the zero component at q
-- statement:
--   Let $W$ be a Weierstrass equation over $\mathbb{Z}$ and $q$ a prime number such that $\Delta(W)\neq 0$, $q\mid\Delta(W)$ and $q\nmid c_4(W)$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying the project's predicate [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16) for $q$, which unfolds to: the image of $q$ in $\overline{\mathbb{Q}}$ is a nonunit of $A$ (so $A$ is a valuation ring of $\overline{\mathbb{Q}}$ whose maximal ideal contains $q$). Write $E$ for the base change to $\overline{\mathbb{Q}}$ of the curve $W$ viewed over $\mathbb{Q}$ via `Int.castRingHom ℚ`, with its group of affine Weierstrass points. The theorem asserts: for every $\sigma$ in `A.inertiaSubgroupIn ℚ` — the project's subgroup of $\overline{\mathbb{Q}}\simeq_{\mathbb{Q}}\overline{\mathbb{Q}}$ obtained as the image of the inertia subgroup of $A$ under the inclusion of the decomposition subgroup — and every point $P$ of $E$, the difference $\sigma\cdot P - P$ satisfies `W.InZeroComponentAt A`, where $\sigma$ acts on points through the project's action by `Point.map` of $\sigma$ on coordinates. The predicate `W.InZeroComponentAt A Q` is the project's own and unfolds to: either $Q = 0$, or $Q = (x,y)$ for a nonsingular point of the affine equation such that either $x\notin A$, or $x,y\in A$ and the residues of $x$ and $y$ in the residue field of $A$ form a nonsingular point of the reduction of $W$ over that residue field. No minimality, no choice of auxiliary prime $\ell$ and no torsion hypothesis enter; the statement is for all points of $E(\overline{\mathbb{Q}})$.
--
--   Classically this is the statement that, at a prime of multiplicative (nodal) reduction, inertia acts trivially on the component group $E/E^0$, equivalently that $\sigma(u)/u$ is a unit in Tate-curve coordinates; it appears in this form in Darmon–Diamond–Taylor and in Silverman's treatment of the Tate curve. Here the hypotheses $q\mid\Delta$, $q\nmid c_4$ stand in for multiplicative reduction of the given integral model, the "zero component" is the project's explicit condition on residues of the coordinates rather than a component group of a Néron model, and the conclusion is asserted for inertia only (it would fail for the full decomposition group in the non-split case). It is the input to the construction of inertia-stable filtrations on $p^m$-torsion ([`WeierstrassCurve.exists_atP_filtration_of_multiplicativeReduction`](thm.html#WeierstrassCurve.exists_atP_filtration_of_multiplicativeReduction) and its variant for all primes), to the unipotence of inertia on $p$-torsion for semistable models, and through these to the Frey-curve statements ruling out Galois-stable lines.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, W.InZeroComponentAt A (σ • P - P) := by sorry
