-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_theorem21
-- name    : QAlgorithms.Papers.Independent.Support50.P38.theorem21
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:08:50.263403+00:00
-- url     : https://prove2.me/theorems/4d6b96f9-2fc3-4dff-9add-ad88facdbaf0
-- title:
--   Quantum fixed-error strong converse with corrected logarithm
-- statement:
--   Let $X$ be finite nonempty, $P$ a probability law, and $\rho_x$ density matrices on a fixed finite nonzero-dimensional Hilbert space. Let $M(n,\lambda)$ be the minimum positive code dimension over all visible maps into normalized code states followed by a linear completely positive trace-preserving decoder, with no shared randomness and $P^n$-average half trace norm error at most $\lambda$ against $\rho_{x_1}\otimes\cdots\otimes\rho_{x_n}$. Write
--
--   $$
--   \chi=S\left(\sum_xP(x)\rho_x\right)-\sum_xP(x)S(\rho_x),
--   $$
--   where $S$ is von Neumann entropy in bits. For every fixed $0<\lambda<1$,
--
--   $$
--   \liminf_{n\to\infty}\frac{\log_2M(n,\lambda)}n\ge\chi.
--   $$
--   This is the quantum strong converse lower bound.
--
--   **Source correction.** The printed theorem omits the logarithm. Its definition of $M$ as a dimension, the exponential bound in its proof, and Question 24 require $\log_2M$.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 10, Theorem 21

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- Theorem 21, PDF pp.10–11: quantum fixed-error strong converse.
SOURCE CORRECTION: insert log_2 before M. The printed display omits log, although p.10
defines M as dim C, p.11 proves an exponential dimension bound, and Question 24 includes log.
The p.11 success-prefactor inversion is also a proof typo and is not assumed here. -/
theorem theorem21 {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B] (p : A → ℝ) (rho : A → Matrix B B ℂ)
    (hp : IsLaw p) (hrho : ∀ a, QAlgorithms.IsDensityMatrix (rho a))
    (error : ℝ) (he : 0 < error) (he1 : error < 1) :
    labelInformation p rho ≤ Filter.liminf (quantumSizeRate p rho error) atTop := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
