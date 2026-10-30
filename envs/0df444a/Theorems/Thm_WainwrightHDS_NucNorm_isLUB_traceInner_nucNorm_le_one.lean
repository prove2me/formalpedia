-- Prove2me | Theorems.Thm_WainwrightHDS_NucNorm_isLUB_traceInner_nucNorm_le_one
-- name    : WainwrightHDS.NucNorm.isLUB_traceInner_nucNorm_le_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:32:48.393894+00:00
-- url     : https://prove2.me/theorems/8fc86c8e-3e44-474d-915f-3514c782e7e6
-- title:
--   Exercise 9.4(c) — the dual norm of the nuclear norm is the $\ell_2$-operator norm
-- statement:
--   For a norm $\Phi$ on $\mathbb R^{d_1\times d_2}$ the dual norm is $\Phi^*(N):=\sup_{\Phi(M)\le1}\langle\!\langle M,N\rangle\!\rangle$. For the nuclear norm $\Phi=|||\cdot|||_{\mathrm{nuc}}$ and every $N\in\mathbb R^{d_1\times d_2}$,
--
--   $$
--   \Phi^*(N) \;=\; \sup_{|||M|||_{\mathrm{nuc}}\le 1} \langle\!\langle M,N\rangle\!\rangle \;=\; |||N|||_2 \;:=\; \sup_{\|z\|_2=1}\|Nz\|_2 .
--   $$
--
--   Thus the "good event" $\{\Phi^*(\nabla\mathcal L_n(\Theta^*))\le\lambda_n/2\}$ of the general theory becomes, for nuclear-norm regularization, a bound on the spectral norm of the gradient; this is how the event $\mathbb G(\lambda_n)$ of Proposition 10.6 arises.
--
--   Differences from the source:
--   - encoding: Φ*(N) = |||N|||₂ with Φ* a supremum → IsLUB {⟨⟨M, N⟩⟩ : |||M|||_nuc ≤ 1} (opNorm2 N); reason: equality with the supremum of a nonempty bounded set is exactly being its least upper bound
--   - encoding: |||N|||₂ := sup_{‖z‖₂=1} ‖Nz‖₂ → operator norm of z ↦ Nz between Euclidean spaces; reason: equal for d₂ ≥ 1; for d₂ = 0 both sides of the claim are 0
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, Exercise 9.4(c), p. 308 (PDF p. 328); dual norm Eq. (9.27), p. 272 (PDF p. 292)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_traceInner
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2

namespace WainwrightHDS.NucNorm

/-- **Exercise 9.4(c): the dual norm of the nuclear norm is the ℓ₂-operator norm.** For every
`N ∈ ℝ^{d₁×d₂}`, `|||N|||₂` is the least upper bound of `{⟨⟨M, N⟩⟩ : |||M|||_nuc ≤ 1}`, i.e.
`Φ*(N) := sup_{|||M|||_nuc ≤ 1} ⟨⟨M, N⟩⟩ = |||N|||₂`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, Exercise 9.4(c), p. 308 (PDF p. 328); dual norm (9.27), p. 272 (PDF p. 292).

Formalization Note: the supremum is stated as `IsLUB` (it is attained and finite, but no junk
value of `sSup` can make the statement trivial). -/
theorem isLUB_traceInner_nucNorm_le_one {d₁ d₂ : ℕ} (N : Matrix (Fin d₁) (Fin d₂) ℝ) :
    IsLUB {t : ℝ | ∃ M : Matrix (Fin d₁) (Fin d₂) ℝ, nucNorm M ≤ 1 ∧ t = traceInner M N}
      (opNorm2 N) := by sorry

end WainwrightHDS.NucNorm
