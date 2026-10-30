-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P38_qudit_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P38.qudit_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:55:44.206145+00:00
-- url     : https://prove2.me/theorems/f5652273-4d73-4101-b2c1-585f162dd2eb
-- title:
--   General-dimensional SRM average-fidelity lower bound
-- statement:
--   Fix a positive qudit dimension $d$. With $N\geq1$ maximally entangled qudit pairs, let Alice use the normalized square-root measurement of $\sigma_i=d^{-(N-1)}P^+_{A_iB}\otimes I_{\bar A_i}$, using the supported inverse square root and equal kernel completion. This is a POVM and the resulting physical port-selection map is a channel. Its Haar-average pure-input fidelity satisfies
--
--   $$f_{d,N}\geq1-\frac{d(d-1)}{N},\qquad\lim_{N\to\infty}f_{d,N}=1\quad\text{for every fixed }d\geq1.$$
--
--   Negative lower bounds for small $N$ are permitted. This supplies an asymptotically faithful protocol in every finite dimension without claiming general-dimensional SRM optimality.
-- source:
--   Asymptotic teleportation scheme as a universal programmable quantum processor, arXiv:0807.4568v2, PDF p. 4, Unnumbered general-d SRM result

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P38

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions; neither is re-declared in this module.

open QAlgorithms.Papers.Independent.Frontier18.P14 (singlet)

open QAlgorithms.Papers.Independent.Renew46.P01 (SpinPath)

/-- PDF p.4: general-d maximally entangled resource and SRM; the bound concerns
Haar-average fidelity f, including its possibly negative lower bound at small N. -/
theorem qudit_fidelity (d : ℕ) (hd : 0 < d) :
    (∀ N : ℕ, 0 < N →
      IsPOVM (srm (signals d N)) ∧
      IsChannel (teleport (1 : Matrix (Ports d N) (Ports d N) ℂ) (srm (signals d N))) ∧
      1 - (d : ℝ) * ((d : ℝ) - 1) / (N : ℝ) ≤
        QuditFidelity.averageFidelity d hd
          (teleport (1 : Matrix (Ports d N) (Ports d N) ℂ) (srm (signals d N)))) ∧
    Tendsto (fun N : ℕ => QuditFidelity.averageFidelity d hd
      (teleport (1 : Matrix (Ports d N) (Ports d N) ℂ) (srm (signals d N))))
        atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P38

end
