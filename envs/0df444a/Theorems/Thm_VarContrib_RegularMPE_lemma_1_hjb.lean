-- Prove2me | Theorems.Thm_VarContrib_RegularMPE_lemma_1_hjb
-- name    : VarContrib.RegularMPE.lemma_1_hjb
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:31.06998+00:00
-- url     : https://prove2.me/theorems/bcc17e99-825e-4895-ac37-ce74ab21fa9d
-- title:
--   Proof of Lemma 1, part (i), pp. 33–34 — a C² V of (4) satisfies 𝒜V + π = 0 on [θ, b), < 0 on (a, θ), V′ = k on (a, θ], V′ < k on (θ, b)
-- statement:
--   Assume the standing assumptions and Assumptions 1–3. Let $\theta\in I$ and $A$ be such that the function $V$ of (4),
--   $$V(x)=\begin{cases}k(x-\theta)+(R\pi)(\theta)+A\varphi(\theta) & x<\theta,\\ (R\pi)(x)+A\varphi(x) & x\ge\theta,\end{cases}$$
--   is twice continuously differentiable on $I$. Then, with $\mathcal A=\tfrac12\sigma^2\partial_x^2+\mu\partial_x-r$,
--
--   1. $\mathcal AV(x)+\pi(x)=0$ for $x\in I$, $x\ge\theta$;
--   2. $\mathcal AV(x)+\pi(x)<0$ for $x\in I$, $x<\theta$;
--   3. $V'(x)=k$ for $x\in I$, $x\le\theta$;
--   4. $V'(x)<k$ for $x\in I$, $x>\theta$.
--
--   These are the conditions (i)–(ii) of the optimality condition of §2.2 for $V$, and they show that the rate $u$ of (6) is nonnegative.
--
--   **Formalization Note.** The paper proves these facts for the threshold it constructs in the proof of Lemma 1, where $V\in C^2(I)$ is achieved by $A=F(\theta)$ and $\theta$ the unique zero of $L$ in (A.3). The hypothesis that $V$ is $C^2$ on $I$ pins exactly that pair: smoothness at $\theta$ is the condition (A.1).
-- source:
--   Kwon, Game of Variable Contributions to the Common Good under Uncertainty, arXiv:1904.00500v1, pp. 33–34, Appendix A, proof of Lemma 1, part (i)

import Mathlib
import Definitions.Def_VarContrib_RegularMPE_Model
import Definitions.Def_VarContrib_RegularMPE_Setting
import Definitions.Def_VarContrib_RegularMPE_Game

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace VarContrib.RegularMPE

/-- Proof of Lemma 1, part (i) (Kwon, pp. 33–34): if `V` of (4) is `C²` on `I`, then
`𝒜V + π = 0` on `[θ, b)`, `𝒜V + π < 0` on `(a, θ)`, `V′ = k` on `(a, θ]` and `V′ < k` on
`(θ, b)`. -/
theorem lemma_1_hjb {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω)
    (hst : Standing m S) (θ A : ℝ) (hθ : θ ∈ m.I)
    (hV : ContDiffOn ℝ 2 (Vsol m S θ A) m.I) :
    (∀ x ∈ m.I, θ ≤ x → gen m (Vsol m S θ A) x + m.π x = 0) ∧
    (∀ x ∈ m.I, x < θ → gen m (Vsol m S θ A) x + m.π x < 0) ∧
    (∀ x ∈ m.I, x ≤ θ → deriv (Vsol m S θ A) x = m.k) ∧
    (∀ x ∈ m.I, θ < x → deriv (Vsol m S θ A) x < m.k) := by sorry

end VarContrib.RegularMPE
