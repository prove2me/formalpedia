-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_otp_perfect
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.otp_perfect
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T19:07:41.023642+00:00
-- url     : https://prove2.me/theorems/30ef1a30-4286-4177-8487-45d538fd1943
-- title:
--   §2.2: perfect one-time-pad security
-- statement:
--   Fix a message length $n\ge0$ and a bit string $x\in\{0,1\}^n$. The real one-time pad uses a fresh uniform shared key $k$, forwards $y=x\oplus k$ authentically, and outputs $(y\oplus k,y)$ to Bob and Eve. The ideal channel outputs $x$ to Bob, and its simulator samples an independent uniform $n$-bit string for Eve. Their output laws $P_x$ and $Q_x$ satisfy
--
--   $$P_x=Q_x,\qquad p_g(P_x,Q_x)=\tfrac12\quad\text{for every randomized decision rule }g.$$
--
--   Here $p_g$ is the success probability in distinguishing the two laws with equal priors. Equality of these complete one-input output kernels gives the perfect security of Figures 2.3 and 2.5, including arbitrary contexts choosing the classical input.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 13, §2.2: perfect one-time-pad security

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P44

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceFirst)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Frontier18.P08 (conditionalEntropyNats)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.13, §2.2: perfect one-time-pad security for Figures 2.3 and 2.5.
Both output kernels coincide, and every randomized black-box test has equal-prior
success exactly one half. The channel used here faithfully delivers ciphertexts. -/
theorem otp_perfect (n : ℕ) (x : Fin n → Bool) :
    otpReal x = otpIdeal x ∧
    ∀ g : ((Fin n → Bool) × (Fin n → Bool)) → Set.Icc (0 : ℝ) 1,
      binaryTestSuccess (otpReal x) (otpIdeal x) g = 1 / 2 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
