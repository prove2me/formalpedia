-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P14_qid_user_security
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P14.qid_user_security
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:22:39.659843+00:00
-- url     : https://prove2.me/theorems/d4bc0fcd-e8ec-4310-888c-0a409bead8fe
-- title:
--   Q-ID user security against a storage-bounded server
-- statement:
--   Fix Q-ID with block length $n$, $m$ passwords, code minimum distance at least $d$, and finite nonempty strongly universal-2 hash families with $\ell$-bit outputs. Let $W$ be any password distribution with $H_{\min}(W)\ge1$. Consider any server attack initially independent of $W$, with unrestricted classical information and computation, whose retained quantum dimension is at most $2^q$ immediately before $\theta,f$ are revealed at step 3. For every $0<\lambda<1/4$, the actual final view $E_{S^*}$ admits a classical extension $W'$ independent of $W$ such that
--
--   $$\delta\!\left(\rho_{WW'E_{S^*}\mid W'\ne W},\rho_{W\leftrightarrow W'\leftrightarrow E_{S^*}\mid W'\ne W}\right)\le 2^{-\frac12((\frac14-\lambda)d-\log_2m-q-\ell-1)}+2^{-(\sigma(\lambda)d-\log_2m-3)},$$
--
--   where $\delta$ is half the trace norm and
--
--   $$\sigma(\lambda)=\frac{\lambda^2\log_2e}{32(2-\log_2\lambda)^2}.$$
--
--   The extension preserves the actual output marginal exactly, and the comparison uses its own conditioned Markov reconstruction. No positive linear slack is assumed, and the finite error bound may exceed one.
-- source:
--   Secure Identification and QKD in the Bounded-Quantum-Storage Model, arXiv:0708.2557v3, PDF p. 10, Proposition3.4: Q-ID user security

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P14

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

open QAlgorithms.Papers.Independent.Gap48.P11 (blockMatrix cqDistance)

open QAlgorithms.Papers.Independent.Claimed50.P31 (bb84Vector)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Positive list length and inhabited fibers supply the tagged union's inhabitant.
This derived instance adds no hypothesis to Lemma 2.2. -/
local instance {m : ℕ} [NeZero m] {A : Fin m → Type*}
    [∀ i, Nonempty (A i)] : Nonempty (Sigma A) :=
  ⟨⟨0, Classical.choice (inferInstance : Nonempty (A 0))⟩⟩

/-- PDF p.10, Proposition 3.4, with Definition 3.2 on p.8.
All admissible server attacks are quantified before the independent extension;
there is no assumed entropy estimate or assumed security witness. -/
theorem qid_user_security
    {n ell m d q : ℕ} {F : Type*} {G Y E : Type}
    [Fintype F] [Nonempty F] [Fintype G] [Nonempty G]
    [Fintype Y] [Nonempty Y] [Fintype E] [Nonempty E]
    (P : QIDParameters n ell m d F G) (W : Law (Fin m))
    (hW : ∀ w, W.prob w ≤ 1 / 2) (lambda : ℝ)
    (hlambda : 0 < lambda) (hlambdaUpper : lambda < 1 / 4)
    (A : ServerAttack n ell q F G Y E) :
    HasIndependentGuess (J := Fin m) (serverOutput P W A) some
      (Real.rpow 2 (-((1 / 4 - lambda) * d - Real.logb 2 m - q - ell - 1) / 2) +
        Real.rpow 2 (-(qidUncertaintyExponent lambda * d - Real.logb 2 m - 3))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P14

end
