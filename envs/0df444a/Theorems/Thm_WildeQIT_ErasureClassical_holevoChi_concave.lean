-- Prove2me | Theorems.Thm_WildeQIT_ErasureClassical_holevoChi_concave
-- name    : WildeQIT.ErasureClassical.holevoChi_concave
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:39.883357+00:00
-- url     : https://prove2.me/theorems/d3d6951a-ce7f-4eab-8adc-d6cf2ac55009
-- title:
--   Theorem 13.3.3: the Holevo information is concave in the input distribution
-- statement:
--   Let $\mathcal N$ be a quantum channel, $\mathcal X$ a finite alphabet, $\{\rho^x\}_{x\in\mathcal X}$ density operators on the channel input, $p_X$ and $q_X$ probability distributions on $\mathcal X$, and $0\le\lambda\le1$. Define the classical–quantum states
--
--   $$
--   \sigma_{XB}=\sum_x p_X(x)|x\rangle\langle x|_X\otimes\mathcal N(\rho^x),\qquad
--   \tau_{XB}=\sum_x q_X(x)|x\rangle\langle x|_X\otimes\mathcal N(\rho^x),
--   $$
--
--   $$
--   \omega_{XB}=\sum_x\big[\lambda p_X(x)+(1-\lambda)q_X(x)\big]|x\rangle\langle x|_X\otimes\mathcal N(\rho^x).
--   $$
--
--   Then
--
--   $$
--   \lambda\,I(X;B)_\sigma+(1-\lambda)\,I(X;B)_\tau\;\le\;I(X;B)_\omega .
--   $$
--
--   With the signal states fixed, the Holevo information is a concave function of the input distribution, so the product-state capacity of a cq channel is a concave maximization.
--
--   **Formalization Note** $I(X;B)$ is evaluated as $H(B)-H(B|X)=H(\sum_x p_X(x)\mathcal N(\rho^x))-\sum_x p_X(x)H(\mathcal N(\rho^x))$ with the published `HolevoCQ.holevoChi` (base-2 von Neumann entropy); the mixing weight $\lambda$ is called `t` in Lean.
--
--   Differences from the source:
--   - encoding: I(X; B) of the cq states σXB, τXB, ωXB → HolevoCQ.holevoChi (H of the average output minus the average output entropy) of the states N(ρx) and the weights; reason: for a classical–quantum state I(X; B) = H(B) − H(B|X), which is this expression (13.114)
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.3.3, (13.109)–(13.112), p. 405

import Definitions.Def_HolevoCQ_holevoChi
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_FinDist

namespace WildeQIT.ErasureClassical

/-- **Theorem 13.3.3** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
p. 405): "The Holevo information `I(X; B)` is concave in the input distribution when the signal
states are fixed, in the sense that `λ I(X; B)_σ + (1 − λ) I(X; B)_τ ≤ I(X; B)_ω` (13.109), where
`σ_{XB}` and `τ_{XB}` are of the form `σ_{XB} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ N(ρˣ)` (13.110),
`τ_{XB} ≡ ∑ₓ q_X(x)|x⟩⟨x|_X ⊗ N(ρˣ)` (13.111), and `ω_{XB}` is a mixture of the states `σ_{XB}`
and `τ_{XB}` of the form `ω_{XB} ≡ ∑ₓ [λ p_X(x) + (1 − λ) q_X(x)] |x⟩⟨x|_X ⊗ N(ρˣ)` (13.112),
where `0 ≤ λ ≤ 1`."

**Formalization Note.** The alphabet is an arbitrary finite type `X`; `p_X`, `q_X` are
probability distributions on it; the signal states `ρˣ` are density operators on the channel
input; `I(X; B)` is the published `HolevoCQ.holevoChi` (`H(B) − H(B|X)`, base-2 von Neumann entropy); the mixing weight `λ` is named `t`. -/
theorem holevoChi_concave {a b X : Type} [Fintype a] [Fintype b] [Fintype X] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) (ρ : X → Matrix a a ℂ)
    (hρ : ∀ x, IsDensityOperator (ρ x)) (p q : FinDist X) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * HolevoCQ.holevoChi (fun x => N.apply (ρ x)) p.prob +
        (1 - t) * HolevoCQ.holevoChi (fun x => N.apply (ρ x)) q.prob ≤
      HolevoCQ.holevoChi (fun x => N.apply (ρ x)) (fun x => t * p.prob x + (1 - t) * q.prob x) := by sorry

end WildeQIT.ErasureClassical
