-- Prove2me | Theorems.Thm_TightQLB_eq_25
-- name    : TightQLB.eq_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:05:43.367548+00:00
-- url     : https://prove2.me/theorems/61c6e509-a1c5-4595-aee4-523570710981
-- title:
--   §4.1, Eq. (25) — degree bound: $(\Psi_t)_S=0$ for $|S|>t$, and $\langle\Phi,D\Phi\rangle\le t\|\Phi\|^2$
-- statement:
--   For a normal-form experiment in the Fourier ensemble and $0\le t\le q$,
--
--   $$
--   (\Psi_t)_S=0\quad\text{whenever }|S|>t,\qquad\text{hence}\qquad\langle\Phi,D\Phi\rangle\le t\|\Phi\|^2
--   $$
--
--   for every $\Phi$ obtained from $\Psi_t$ by applying operators that act pointwise.
--
--   The first part says that the state after $t$ queries is a polynomial of degree at most $t$ in the values of $f$, as in the polynomial method.
--
--   Differences from the source:
--   - encoding: "We fix an experiment …, which by Lemma 3.2 we may assume makes a fixed sequence of q controlled queries" (p. 21) → B : NormalForm n q (Qubits n × Bool) W E, for every finite W and E; reason: the paper's standing convention for §4; Lemma 3.2 (milestone) is the bridge
--   - generalization: "Throughout, n ≥ 1" (p. 13) → every n : ℕ, with no hypothesis on n; reason: the argument does not use n ≥ 1, and the instances with n ≥ 1 are the source's statement
--   - encoding: "every Φ that is obtained from Ψ_t by applying operators that act pointwise" → pw T Ψ_t for an arbitrary matrix T on H; reason: a composition of pointwise operators is pointwise, and T = 1 gives Ψ_t
--   - encoding: ⟨Φ, DΦ⟩ → its real part; reason: the form is real, since D is a sum of projections
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §4.1, Eq. (25), p. 24 (PDF p. 27)

import Mathlib
import Definitions.Def_TightQLB_RecordingState
open QAlgorithms

namespace TightQLB

/-- **§4.1, Eq. (25) (degree bound)**, p.24 (PDF p.27).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"By induction on t, (Ψ_t)_S = 0 whenever |S| > t, hence ⟨Φ, DΦ⟩ ≤ t ‖Φ‖² (25) for every Φ that is
obtained from Ψ_t by applying operators that act pointwise, such as P^c_x or Π_z."

**Formalization Note.** `B` is an experiment in the normal form of Lemma 3.2 and `Ψ_t = B.stateFn t`.
"Obtained from `Ψ_t` by applying operators that act pointwise" is `pw T Ψ_t` for an arbitrary matrix
`T` on `H = A ⊗ E` (a composition of pointwise operators is pointwise; `T = 1` gives `Ψ_t`).
`⟨Φ, DΦ⟩` is real, and its real part is taken. `n ≥ 1` is not needed. -/
theorem eq_25 {n q : ℕ} {W E : Type} [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]
    (B : NormalForm n q (Qubits n × Bool) W E) (t : Fin (q + 1)) :
    (∀ S : Finset (Qubits n), (t : ℕ) < S.card → coeff (B.stateFn t) S = 0) ∧
    (∀ T : Matrix (Reg (Qubits n × Bool) W × E) (Reg (Qubits n × Bool) W × E) ℂ,
      (ip (pw T (B.stateFn t)) (Dop (pw T (B.stateFn t)))).re ≤
        (t : ℝ) * nsq (pw T (B.stateFn t))) := by sorry

end TightQLB
