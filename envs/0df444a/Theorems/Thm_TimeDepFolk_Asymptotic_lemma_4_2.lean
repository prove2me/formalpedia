-- Prove2me | Theorems.Thm_TimeDepFolk_Asymptotic_lemma_4_2
-- name    : TimeDepFolk.Asymptotic.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:12.609458+00:00
-- url     : https://prove2.me/theorems/2771e237-80fc-4617-86e3-1b48149408a6
-- title:
--   Lemma 4.2, p. 15 — for patient θ^k, θ^k_1[T] → 0 uniformly in T and θ^k_t[T]/θ^k_{t+1}[T] → 1 uniformly in T and t
-- statement:
--   Let $(\theta^k)_{k\ge1}$ be a sequence of patient evaluations, and write $\theta^k[T]$ for the continuation evaluation from stage $T$ on, $\theta^k_t[T]=\theta^k_{T-1+t}/\sum_{s\ge T}\theta^k_s$. Then
--
--   1. $\theta^k_1[T]\to0$ as $k\to\infty$, uniformly in $T\ge1$;
--   2. $\dfrac{\theta^k_t[T]}{\theta^k_{t+1}[T]}\to1$ as $k\to\infty$, uniformly in both $T\ge1$ and $t\ge1$.
--
--   In other words, every continuation of a patient sequence is again patient, uniformly over the starting stage, and its first weight vanishes. This is what lets the equilibrium construction restart at any stage with the same parameters.
--
--   **Formalization Note.** `cont (θ k).θ n` is the paper's $\theta^k[n+1]$ (0-based stages), and part 2 is stated for the pair $(n,s)$ jointly, which is uniformity in both indices. The page writes the middle term of part 2 as $\theta^k_{T-1+t}[T]/\theta^k_{T+t}[T]$; by the definition of $\theta[T]$ it is $\theta^k_{T-1+t}/\theta^k_{T+t}$ (without $[T]$), a printed slip. Only the left-hand ratio is stated here.
-- source:
--   X. Li, The folk theorem for repeated games with time-dependent discounting, SSRN Working Paper 3407197 (version of August 16, 2019), p. 15, Lemma 4.2

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TimeDepFolk.Asymptotic

theorem lemma_4_2 (θ : ℕ → Evaluation) (hθ : IsPatient θ) :
    TendstoUniformly (fun k n => cont (θ k).θ n 0) (fun _ => (0 : ℝ)) Filter.atTop ∧
      TendstoUniformly
        (fun k (p : ℕ × ℕ) => cont (θ k).θ p.1 p.2 / cont (θ k).θ p.1 (p.2 + 1))
        (fun _ => (1 : ℝ)) Filter.atTop := by sorry

end TimeDepFolk.Asymptotic
