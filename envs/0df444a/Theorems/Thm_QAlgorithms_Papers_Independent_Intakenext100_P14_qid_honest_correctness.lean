-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P14_qid_honest_correctness
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P14.qid_honest_correctness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:21:43.824434+00:00
-- url     : https://prove2.me/theorems/f5cd77ea-30fd-43b1-ab65-4568094a2dc5
-- title:
--   Exact honest correctness of Q-ID on the ideal channel
-- statement:
--   Fix the Q-ID parameters: a public injective binary basis code $c$ of length $n$ on $m$ passwords, with minimum distance at least $d$, and finite nonempty strongly universal-2 hash families $F,G$ with $\ell$-bit outputs. Let both honest parties use the same password $w$. The user independently samples uniform $x,\theta$, sends $|x\rangle_\theta$, and reveals independently sampled $f$. The server measures in $c(w)$, obtaining $x'$, and returns independently sampled $g$. Let $I_w=\{i:\theta_i=c(w)_i\}$ and let restriction pack the selected bits in increasing order, followed by zero padding. The server tests equality of $f(x|_{I_w})\oplus g(w)$ and $f(x'|_{I_w})\oplus g(w)$. On the ideal channel,
--
--   $$\Pr[\text{server accepts}]=1.$$
--
--   The probability is computed from the actual BB84 Born rule and the four independent uniform choices. This exact acceptance property on the ideal channel implies Definition 3.1.
-- source:
--   Secure Identification and QKD in the Bounded-Quantum-Storage Model, arXiv:0708.2557v3, PDF p. 10, §3.3, unnumbered honest Q-ID correctness

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

/-- PDF p.10 (Definition 3.1 on p.8): Q-ID accepts honest equal passwords
with probability exactly one on the ideal channel. -/
theorem qid_honest_correctness
    {n ell m d : ℕ} {F G : Type*} [Fintype F] [Nonempty F]
    [Fintype G] [Nonempty G] (P : QIDParameters n ell m d F G) (w : Fin m) :
    honestAcceptance P w = 1 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P14

end
