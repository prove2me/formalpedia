-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_interior_open_set_reachable
-- name    : StochKolmogorov.Classify.interior_open_set_reachable
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-03T22:52:41.557451+00:00
-- url     : https://prove2.me/theorems/c91a121b-0fdc-4f39-bc58-4eee3c4a0838
-- title:
--   From every interior point the stochastic Kolmogorov system enters every nonempty open subset of the open orthant with positive probability
-- statement:
--   Let $X^x$ ($x\in\mathbb R^n_+$) solve the stochastic Kolmogorov system (1.1) $dX_i=X_i f_i(X)\,dt+X_i g_i(X)\,dE_i$, $E=\Gamma^\top B$, on a common Brownian motion $B$, with $f_i,g_i$ locally Lipschitz on $\mathbb R^n_+$ and the diffusion matrix $(g_i(x)g_j(x)\sigma_{ij})_{ij}$ positive definite on $\mathbb R^n_+$. Then for every $x$ in the open orthant $\mathbb R^{n,\circ}_+$ and every nonempty open $U\subseteq\mathbb R^{n,\circ}_+$ there is $t\ge 0$ with
--
--   $$\mathbb P\big(X^x_t\in U\big)>0 .$$
--
--   Role: the irreducibility of the process in the interior used at the end of the proof of Theorem 5.2 (every ergodic measure on the boundary attracts the process with positive probability from every interior point): one steers from $x$ into a neighbourhood of an arbitrary point of $U$ by the local minorization of the transition laws on compact boxes of the open orthant.
--
--   **Formalization Note**: the solution family is the one of the definitions file (each $X^x$ a strong solution started at $x$ on the same Brownian motion); the probability is the measure of the event, no measurability of $U$ beyond openness is needed.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, Lemma 3.6 and its proof in the Appendix (p. 32: transition probabilities of the nondegenerate diffusion started in a compact subset of the interior are minorized, P(t,x,B) >= m(B)), used for irreducibility in the proof of Theorem 5.2 (Section 5)

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify

open EthierKurtz

theorem interior_open_set_reachable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hpd : ∀ x ∈ orthant n, (Matrix.of fun i j => C.g i x * C.g j x * C.sig i j).PosDef) :
    ∀ x ∈ openOrthant n, ∀ U : Set (SDEState n), IsOpen U → U.Nonempty →
      U ⊆ openOrthant n → ∃ t : ℝ≥0, 0 < P {ω | X x t ω ∈ U} := by sorry

end StochKolmogorov.Classify
