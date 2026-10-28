-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_procrustean_filter
-- name    : QAlgorithms.Papers.Independent.Support50.P42.procrustean_filter
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:18:09.507282+00:00
-- url     : https://prove2.me/theorems/438e0a14-0aed-45e8-a49f-f2ae9721f9f4
-- title:
--   Procrustean filtering in finite Schmidt rank
-- statement:
--   Let $d>0$ and let $c_1,\ldots,c_d\ge0$ satisfy $\sum_i c_i^2=1$. Put $a=\min_i c_i$. For the Schmidt state $\sum_i c_i|i,i\rangle$, Alice's successful filter is $F=\operatorname{diag}(a/c_i)$, using the totalized value zero at a zero amplitude; its complementary failure filter is $G=\operatorname{diag}\sqrt{1-(a/c_i)^2}$. They form a complete instrument, and
--
--   $$\Pr(\mathrm{success})=d a^2,\qquad (F\otimes I)|\psi\rangle=\sqrt{d a^2}\,\frac1{\sqrt d}\sum_i|i,i\rangle.$$
--
--   The positive-probability normalized branch is maximally entangled. For a qubit bias $p$, success is $2\min(p,1-p)$, zero at product endpoints and one at maximal entanglement. This constructs concentration without an optimality claim. The source's printed absorbed fraction $\tan^2\theta$ is corrected to the retained fraction, as required by equal successful amplitudes.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 9, §III: one-pair Procrustean concentration and finite-rank extension

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.9: finite-rank Procrustean filter, including zero Schmidt amplitudes.
Printed absorption tan squared theta is corrected to RETENTION of that
fraction, as uniquely fixed by equalization of successful amplitudes. -/
theorem procrustean_filter (d : ℕ) (hd : 0<d) (c : Fin d → ℝ)
    (hc : ∀ i, 0≤c i) (hnorm : ∑ i, (c i)^2=1) :
    IsKrausFamily (fun j : Fin 2 => if j=0 then procrusteanSuccess c else filterFailure c) ∧
    pureDensity (aliceKetBranch (procrusteanSuccess c) (diagonalKet c))=
      ((((d : ℝ)*(leastAmplitude c)^2 : ℝ)) : ℂ) • pureDensity (uniformKet d) ∧
    ‖aliceKetBranch (procrusteanSuccess c) (diagonalKet c)‖^2=(d : ℝ)*(leastAmplitude c)^2 ∧
    (0<leastAmplitude c →
      ((Real.sqrt ((d : ℝ)*(leastAmplitude c)^2))⁻¹ : ℂ) •
        aliceKetBranch (procrusteanSuccess c) (diagonalKet c)=uniformKet d) ∧
    (∀ p : ℝ, 0≤p → p≤1 →
      (2 : ℝ)*(leastAmplitude (fun i : Fin 2 => if i=0 then Real.sqrt (1-p) else Real.sqrt p))^2=
        procrusteanYield p) := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
