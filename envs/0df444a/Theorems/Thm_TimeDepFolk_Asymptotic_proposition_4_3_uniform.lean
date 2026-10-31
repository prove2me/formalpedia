-- Prove2me | Theorems.Thm_TimeDepFolk_Asymptotic_proposition_4_3_uniform
-- name    : TimeDepFolk.Asymptotic.proposition_4_3_uniform
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:15.552554+00:00
-- url     : https://prove2.me/theorems/b0cd9393-0146-4faf-87f9-9f37f77b4daf
-- title:
--   §5.1 Part B, p. 19 — Proposition 4.3 for the continuation evaluations θ^k[T], with K(η) independent of T and of the target
-- statement:
--   Under the hypotheses of Proposition 4.3, the threshold $K(\eta)$ can also be taken independent of the stage at which the path starts. Precisely: for every $\eta>0$ there is $K(\eta)$ such that for every $k\ge K(\eta)$, every starting stage $T_0\ge1$ and every $x\in\mathcal F$ there is a pure action sequence $\mathbf x=(a_t)_{t\ge1}$ with
--
--   1. $\gamma_{\theta^k[T_0]}(\mathbf x)=x$;
--   2. $\big\|\gamma_{\theta^k[T_0][t+1]}(\mathbf x^t)-x\big\|_\infty\le\eta$ for all $t\ge1$, where $\mathbf x=(a_1,\dots,a_t,\mathbf x^t)$.
--
--   In the proof of Theorem 3.1 the rewarding phases start at arbitrary stages, so each reward path is evaluated by a different continuation evaluation; this statement supplies all of them with one $K(\eta)$.
--
--   **Formalization Note.** The page states this for the finitely many vectors $w[z_0],\dots,w[z_I]$, which lie in $\mathcal F$; quantifying over all $x\in\mathcal F$ is that claim with the vectors abstracted (and is what Proposition 4.3's uniformity in $x$ gives). The start stage is 0-based: `cont (θ k).θ n` is $\theta^k[n+1]$, and `cont (cont (θ k).θ n) T` is its continuation after $T$ more stages. The page writes condition 2 as $\|\gamma_{\theta^k[t]}(\mathbf x^t[i])-w[z_i]\|_\infty\le\eta$; the evaluation meant is the continuation of $\theta^k[T_i]$ after $t$ stages, as in Proposition 4.3 ii), and that is what is stated.
-- source:
--   X. Li, The folk theorem for repeated games with time-dependent discounting, SSRN Working Paper 3407197 (version of August 16, 2019), p. 19, §5.1 Part B (application of Proposition 4.3 with Lemma 4.2)

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TimeDepFolk.Asymptotic

theorem proposition_4_3_uniform {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    (g : I → (∀ i, A i) → ℝ) (θ : ℕ → Evaluation) (hθ : IsPatient θ) :
    ∀ η > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ n : ℕ, ∀ x ∈ F g, ∃ h : ℕ → (∀ i, A i),
      purePayoff g (cont (θ k).θ n) h = x ∧
        ∀ T ≥ 1,
          ‖purePayoff g (cont (cont (θ k).θ n) T) (fun s => h (T + s)) - x‖ ≤ η := by sorry

end TimeDepFolk.Asymptotic
