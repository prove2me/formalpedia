-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P45_classicalReverseShannon
-- name    : QAlgorithms.Papers.Independent.Dependency50.P45.classicalReverseShannon
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:09:36.760994+00:00
-- url     : https://prove2.me/theorems/5c1f32e2-a75f-408a-966c-e515d8d0a226
-- title:
--   Theorem 2: classical reverse Shannon theorem
-- statement:
--   Let $N(y\mid x)$ be a discrete memoryless channel on finite nonempty alphabets $X,Y$, with nonnegative probabilities summing to one in $y$. Let $C=\max_q I_q(X:Y)$ be its Shannon capacity in bits, and fix $\varepsilon>0$. There is a sequence of protocols $S_n$, chosen independently of the channel input, using only forward noiseless bits and an unlimited independent fair Bernoulli tape shared beforehand. The protocol is deterministic conditional on this tape; Bob uses only the tape and transmitted bit string. With $m_n(x)$ the transmitted length, for every finite block, input, and output,
--
--   $$\Pr[S_n(x)=y]=\prod_{j=1}^n N(y_j\mid x_j),\qquad \lim_{n\to\infty}\max_{x\in X^n}\Pr\bigl[m_n(x)>n(C+\varepsilon)\bigr]=0.$$
--
--   The simulation is exact at every block size, including zero, and the cost guarantee is a uniform tail bound rather than an expected-length or average-input bound.
-- source:
--   Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem, arXiv:quant-ph/0106052v2, PDF p. 36, Theorem 2: classical reverse Shannon theorem

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

noncomputable section

open scoped ComplexConjugate Matrix

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel)

/-- PDF p.36, Theorem 2, Eqs.(91)--(92): exact finite-block simulation and a
variable-length tail bound uniform in every input. Protocols precede the input. -/
theorem classicalReverseShannon {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (N : DMC X Y) (eps : ℝ) (heps : 0 < eps) :
    ∃ P : (n : ℕ) → ReverseProtocol X Y n,
      (∀ n x y, reverseProb (P n) x y = blockProb N n x y) ∧
      Tendsto (fun n => overflow (P n) ((n : ℝ) * (shannonCapacity N + eps)))
        atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P45

end
