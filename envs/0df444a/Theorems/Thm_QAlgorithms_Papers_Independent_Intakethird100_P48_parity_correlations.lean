-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P48_parity_correlations
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P48.parity_correlations
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:32:54.082564+00:00
-- url     : https://prove2.me/theorems/b72f96a1-dbdd-4f56-b451-384ee13b2d82
-- title:
--   Parallel-XOR distillability depends only on correlators
-- statement:
--   Let $P$ and $Q$ be valid binary non-signaling behaviors, and let $n\ge0$ be an integer. Define $X_{xy}(P)=P(00\mid xy)+P(11\mid xy)-P(01\mid xy)-P(10\mid xy)$. Let $\operatorname{NDP}_n(P)$ be the separate local XORs of $n$ independent copies receiving the same input pair, and write $\operatorname{NL}$ for the maximum absolute CHSH expression. Each output correlator satisfies
--
--   $$
--   X_{xy}(\operatorname{NDP}_n(P))=X_{xy}(P)^n.
--   $$
--
--   If $X_{xy}(P)=X_{xy}(Q)$ for every input pair, then their original non-localities agree, their output non-localities agree, and
--
--   $$
--   \operatorname{NDP}_n\text{ strictly distills }P
--   \quad\Longleftrightarrow\quad
--   \operatorname{NDP}_n\text{ strictly distills }Q.
--   $$
--
--   Strict distillation requires valid non-signaling input/output behaviors and $\operatorname{NL}(\text{output})>\operatorname{NL}(\text{input})>2$. At $n=0$ both outputs are the deterministic pair $00$ and the correlator identity uses the empty-product value $1$. This statement concerns only the presented parallel-XOR protocol, not arbitrary adaptive wirings.
-- source:
--   Distilling Non-Locality, arXiv:0809.3173v4, PDF p. 3, Unnumbered: parity distillability depends only on correlators

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P48

namespace QAlgorithms.Papers.Independent.Intakethird100.P48

open scoped BigOperators TensorProduct

noncomputable section

/-- PDF p.3, marginal-independence observation and proof-used parity identity:
all output correlators are input correlators raised to n. Consequently equal
correlators imply equal original/output NL and the same strict distillability.
Scope is the presented parallel-XOR protocol only. -/
theorem parity_correlations (P Q : Behavior) (n : ℕ)
    (hP : IsBinaryNS P) (hQ : IsBinaryNS Q) :
    (∀ x y, binaryCorrelator (parallelOutputLaw (parityProtocol n) P) x y =
      (binaryCorrelator P x y) ^ n) ∧
    ((∀ x y, binaryCorrelator P x y = binaryCorrelator Q x y) →
      nonlocality P = nonlocality Q ∧
      nonlocality (parallelOutputLaw (parityProtocol n) P) =
        nonlocality (parallelOutputLaw (parityProtocol n) Q) ∧
      (StrictlyDistills (parityProtocol n) P ↔ StrictlyDistills (parityProtocol n) Q)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P48
