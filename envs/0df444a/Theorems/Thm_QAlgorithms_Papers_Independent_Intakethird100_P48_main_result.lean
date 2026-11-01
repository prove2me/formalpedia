-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P48_main_result
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P48.main_result
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:30:47.081876+00:00
-- url     : https://prove2.me/theorems/2db805a9-5841-4111-a0c7-c7594a6274dc
-- title:
--   One parity protocol family distills quantum and post-quantum boxes
-- statement:
--   A binary behavior is a conditional probability table $P(ab\mid xy)$ with $x,y,a,b\in\{0,1\}$. Valid resource and output behaviors are nonnegative, normalized separately at every input pair, and non-signaling in both directions. Write $\operatorname{NL}(P)$ for the maximum absolute three-plus/one-minus CHSH expression over the four input pairs. For $n$ independent identical copies, $\operatorname{NDP}_n$ supplies the same local input to every copy and outputs the local XOR of the resulting bits.
--
--   There is one fixed family $W=(\operatorname{NDP}_n)_{n\ge0}$ of classical local protocols without communication, chosen before the resources, such that
--
--   $$
--   \begin{aligned}
--   &\exists n_Q>1,\ Q\text{ quantum}:\quad \operatorname{NL}(W_{n_Q}(Q))>\operatorname{NL}(Q)>2,\
--   &\exists n_R>1,\ R\text{ non-quantum}:\quad \operatorname{NL}(W_{n_R}(R))>\operatorname{NL}(R)>2.
--   \end{aligned}
--   $$
--
--   Quantum means exact realization of the entire table by local binary measurements on a normalized bipartite quantum state. The two resource claims hold together for the same protocol family. This is the paper's existence result; the following targets give its explicit families.
-- source:
--   Distilling Non-Locality, arXiv:0809.3173v4, PDF p. 2, Main Result (abstract p.1; explicit statement p.2)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P48

namespace QAlgorithms.Papers.Independent.Intakethird100.P48

open scoped BigOperators TensorProduct

noncomputable section

/-- PDF p.2, Main Result (abstract p.1): one fixed local parity protocol family
distills some quantum and some post-quantum binary non-local resources. -/
theorem main_result :
    ∃ W : (n : ℕ) → ParallelProtocol n,
      (∀ n, W n = parityProtocol n) ∧
      (∃ (n : ℕ) (Q : Behavior), 1 < n ∧ IsQuantum Q ∧ StrictlyDistills (W n) Q) ∧
      (∃ (n : ℕ) (R : Behavior), 1 < n ∧ ¬ IsQuantum R ∧ StrictlyDistills (W n) R) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P48
