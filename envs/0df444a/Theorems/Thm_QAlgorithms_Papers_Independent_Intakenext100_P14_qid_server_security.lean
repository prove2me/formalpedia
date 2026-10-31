-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P14_qid_server_security
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P14.qid_server_security
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:23:34.871999+00:00
-- url     : https://prove2.me/theorems/8f3fd9df-3763-4b7e-87fa-d878801d6059
-- title:
--   Q-ID server security against an unrestricted user
-- statement:
--   Fix Q-ID with $m$ passwords, a public injective code of length $n$ and minimum distance at least $d$, and finite nonempty strongly universal-2 hash families with $\ell$-bit outputs. Let $W$ have $H_{\min}(W)\ge1$. For any dishonest user initially independent of $W$, with unrestricted quantum storage and computation, the actual output admits a classical extension $W'\in\mathcal W\cup\{\perp\}$ independent of $W$. The same $W'$ satisfies
--
--   $$\Pr[\text{accept}\mid W\ne W']\le\varepsilon,\qquad \Pr[\text{reject},\ W=W']=0,$$
--
--   and
--
--   $$\delta\!\left(\rho_{WW'E_{U^*}\mid W\ne W'},\rho_{W\leftrightarrow W'\leftrightarrow E_{U^*}\mid W\ne W'}\right)\le\varepsilon,\qquad \varepsilon=\frac{m^2}{2^\ell}.$$
--
--   The final view includes the server's announced decision. Equality acceptance is stated as a weighted event so a zero-probability equality event imposes no artificial positivity requirement. Mismatch has probability at least $1/2$. The execution uses the honest server's actual early measurement in $c(W)$; no intermediate collision or entropy property is assumed.
-- source:
--   Secure Identification and QKD in the Bounded-Quantum-Storage Model, arXiv:0708.2557v3, PDF p. 11, Proposition3.5: Q-ID server security

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

/-- PDF pp.11-12, Proposition 3.5, and Definition 3.3 on p.8.
The user is unbounded. Error is m^2/2^ell after conditioning, and secrecy
includes the final announced accept/reject decision with the SAME witness. -/
theorem qid_server_security
    {n ell m d : ℕ} {F G : Type*} {R E : Type}
    [Fintype F] [Nonempty F] [Fintype G] [Nonempty G]
    [Fintype R] [Nonempty R] [Fintype E] [Nonempty E]
    (P : QIDParameters n ell m d F G) (W : Law (Fin m))
    (hW : ∀ w, W.prob w ≤ 1 / 2) (A : UserAttack n ell F G R E) :
    ServerSecurity (userOutput P W A) ((m : ℝ) ^ 2 / (2 : ℝ) ^ ell) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P14

end
