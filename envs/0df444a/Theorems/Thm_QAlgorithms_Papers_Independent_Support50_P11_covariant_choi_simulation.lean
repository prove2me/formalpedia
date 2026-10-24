-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_covariant_choi_simulation
-- name    : QAlgorithms.Papers.Independent.Support50.P11.covariant_choi_simulation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:10:22.885239+00:00
-- url     : https://prove2.me/theorems/55c4d0f4-a4b0-462e-997f-bfce77c748a2
-- title:
--   §VI (53)–(56): teleportation-covariance sufficient for exact Choi simulation
-- statement:
--   Let $\mathcal N:A'\to B$ be finite CPTP. Let $C$ be a positive finite classical outcome register, $M:A'\widetilde A'\to C$ a CPTP classical-output measurement map, and $U_c,V_c$ unitary corrections on $A',B$. Suppose that $M$ with corrections $U_c$ teleports every input operator exactly using one normalized Bell state and that, for every $c$ and operator $X$,
--   $$\mathcal N(U_c XU_c^\dagger)=V_c\mathcal N(X)V_c^\dagger.$$
--   Let $\nu$ be the computed normalized Choi state of $\mathcal N$. Applying $M$ to the input and Alice's share of $\nu$, sending $c$ forward, and applying $V_c$ on Bob's share gives
--   $$\operatorname{Sim}_{M,V,\nu}(X)=\mathcal N(X)\qquad\text{for every operator }X.$$
--   In particular an exact single-copy Choi simulation exists. The given protocol and corrections are fixed before the input; no simulation identity is assumed for $\nu$.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 10, §VI (53)–(56): teleportation-covariance sufficient for exact Choi simulation

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)

open QAlgorithms.Papers.Independent.Information100.P21 (pt)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

section Statements

variable {I O : Type} [Fintype I] [Nonempty I] [Fintype O] [Nonempty O]

/-- PDF p.10, (53)--(56): the given teleportation measurement and covariant output
corrections construct the simulation on all operators, with one computed Choi state. -/
theorem covariant_choi_simulation
    (N : Superop I O) (hN : IsChannel N) {C : Type*} [Fintype C] [Nonempty C]
    (M : Superop (I × I) C) (hM : IsChannel M) (hclassical : ∀ X, dephasing (M X) = M X)
    (U : C → Matrix.unitaryGroup I ℂ) (V : C → Matrix.unitaryGroup O ℂ)
    (hteleport : ∀ X, resourceSim (choiState (fun Y : Matrix I I ℂ => Y)) M
      (classicalControlledUnitary (fun c => (U c : Matrix I I ℂ))) X = X)
    (hcov : ∀ c X, N (conjSuperop (U c : Matrix I I ℂ) X) =
      conjSuperop (V c : Matrix O O ℂ) (N X)) :
    (∀ X, resourceSim (choiState N) M (classicalControlledUnitary (fun c => (V c : Matrix O O ℂ))) X = N X) ∧
    HasChoiSimulation N := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P11

end
