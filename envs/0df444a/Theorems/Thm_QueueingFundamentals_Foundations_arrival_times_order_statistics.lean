-- Prove2me | Theorems.Thm_QueueingFundamentals_Foundations_arrival_times_order_statistics
-- name    : QueueingFundamentals.Foundations.arrival_times_order_statistics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T06:50:03.845495+00:00
-- url     : https://prove2.me/theorems/fcf39aaa-2f13-4e43-aee5-606316986dc7
-- title:
--   Eq. (1.16) — given k arrivals in [0, L], the arrival times are uniform order statistics
-- statement:
--   Let $T_0,T_1,\dots$ be independent exponential interarrival times with rate $\lambda>0$, with arrival epochs $\tau_i=S_i=T_0+\dots+T_{i-1}$ and counting process $N(t)$. Fix an interval length $L>0$ (the book's $T$) and $k\ge0$. Conditionally on the event $\{N(L)=k\}$, the vector $(\tau_1,\dots,\tau_k)$ has the density
--   $$f_\tau(t_1,\dots,t_k\mid k\text{ arrivals in }[0,L])=\frac{k!}{L^k}\qquad\text{on }\{0<t_1<t_2<\dots<t_k<L\},$$
--   and zero elsewhere. This is the joint density of the order statistics of $k$ independent random variables uniform on $[0,L]$.
--
--   The result underlies the "completely random arrivals" interpretation of the Poisson process and the PASTA property.
--
--   **Formalization Note** The statement is an equality of measures on $\mathbb R^k$: the image of the conditional probability $\mu(\,\cdot\mid N(L)=k)$ under $\omega\mapsto(\tau_1,\dots,\tau_k)$ equals Lebesgue measure on the open ordered simplex with constant density $k!/L^k$. The interval length is called $L$ because $T$ names the interarrival times.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.19–20, Eq. (1.16)

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_ArrivalProcess

open MeasureTheory ProbabilityTheory

namespace QueueingFundamentals.Foundations

/-- Eq. (1.16) (pp.19–20): given `k` arrivals in `[0, L]`, the arrival epochs
`τ_1 < ⋯ < τ_k` have the joint density `k!/L^k` on `{0 < t_1 < ⋯ < t_k < L}`, the density of
the order statistics of `k` independent uniform variables on `[0, L]`. -/
theorem arrival_times_order_statistics {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    (hT : IsExpInterarrivals μ lam T) (L : ℝ) (hL : 0 < L) (k : ℕ) :
    (cond μ {ω | countingProcess T L ω = k}).map
        (fun ω (i : Fin k) => arrivalTime T (i.val + 1) ω) =
      (volume.restrict {s : Fin k → ℝ | StrictMono s ∧ ∀ i, 0 < s i ∧ s i < L}).withDensity
        (fun _ => ENNReal.ofReal ((k.factorial : ℝ) / L ^ k)) := by sorry

end QueueingFundamentals.Foundations
