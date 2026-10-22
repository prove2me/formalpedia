-- Prove2me | Theorems.Thm_QuditSymCircuits_FermionLaw_eq_5
-- name    : QuditSymCircuits.FermionLaw.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:50.843055+00:00
-- url     : https://prove2.me/theorems/0a23149f-baa6-400c-b76c-bbfecddcdaf9
-- title:
--   Eq. (5), p. 3 — a 2-local SU(d)-invariant unitary is a global phase times e^{iθP_ab}
-- statement:
--   Let $V$ be a unitary on $n$ qudits that acts non-trivially on at most the qudits $a$ and $b$ (that is, $V = W_{ab}\otimes\mathbb I_{\text{rest}}$) and commutes with $U^{\otimes n}$ for every $U\in\mathrm{SU}(d)$. Then there are real numbers $\varphi$ and $\theta\in[0,2\pi)$ with
--   $$V = e^{i\varphi}\, e^{i\theta\mathbf P_{ab}} = e^{i\varphi}\big(\cos\theta\,\mathbb I + i\sin\theta\,\mathbf P_{ab}\big),$$
--   where $\mathbf P_{ab}$ is the swap of qudits $a$ and $b$.
--
--   This is the description of the generators of the group $\mathcal V_2$: up to global phases, 2-local SU(d)-invariant circuits are built from exponentials of swaps.
--
--   **Formalization Note.** $a = b$ is allowed (then $V$ acts on one qudit, $\mathbf P_{aa} = \mathbb I$, and the claim is that $V$ is a phase). The range $\theta\in[0,2\pi)$ is the one of Eq. (6); $e^{i\theta\mathbf P_{ab}}$ is written in the closed form of Eq. (5).
-- source:
--   Marvian, Liu and Hulse, Qudit circuits with SU(d) symmetry, arXiv:2105.12877v2, p. 3, Eq. (5) and the sentence before it

import Mathlib
import Definitions.Def_QuditSymCircuits_FermionLaw_Model

open scoped Matrix
open QuditSymCircuits.FermionLaw QAlgorithms.Entanglement

namespace QuditSymCircuits.FermionLaw

theorem eq_5 (n d : ℕ) (a b : Fin n) (V : Matrix.unitaryGroup (Fin n → Fin d) ℂ)
    (hloc : IsLocalOn a b (V : Op n d)) (hinv : IsSUdInvariant (V : Op n d)) :
    ∃ φ θ : ℝ, θ ∈ Set.Ico 0 (2 * Real.pi) ∧
      (V : Op n d) = Complex.exp ((φ : ℂ) * Complex.I) • expInv θ (swapOp a b : Op n d) := by sorry

end QuditSymCircuits.FermionLaw
