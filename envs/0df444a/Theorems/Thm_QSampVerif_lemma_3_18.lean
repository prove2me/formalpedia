-- Prove2me | Theorems.Thm_QSampVerif_lemma_3_18
-- name    : QSampVerif.lemma_3_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:27:10.158409+00:00
-- url     : https://prove2.me/theorems/ffa2e485-1164-41cd-b444-e5d6a53f17ee
-- title:
--   Lemma 3.18 — exponential supermartingale bound $\mathbb E[e^{sB_N}\mathbf 1_A]\le e^{vh}\prod_n c_n$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with filtration $(\mathcal F_n)$, and let $(B_n,D_n)_{n=0}^N$ be adapted real processes with $B_0=D_0=0$. Let $s,v\ge0$ and let deterministic $c_n>0$ satisfy
--
--   $$\mathbb E\bigl[e^{s(B_n-B_{n-1})-v(D_n-D_{n-1})}\bigm|\mathcal F_{n-1}\bigr]\le c_n\qquad(1\le n\le N).$$
--
--   Then
--
--   1. $M_n=e^{sB_n-vD_n}\big/\prod_{i=1}^nc_i$ ($0\le n\le N$) is a nonnegative supermartingale: integrable, adapted and $\mathbb E[M_n\mid\mathcal F_{n-1}]\le M_{n-1}$;
--   2. for every $h\in\mathbb R$ and every terminal event $A\in\mathcal F_N$ with $A\subseteq\{D_N\le h\}$,
--   $$\mathbb E\bigl[e^{sB_N}\mathbf 1_A\bigr]\le e^{vh}\prod_{n=1}^Nc_n.\qquad(42)$$
--
--   The bound turns conditional bounds on each exponential increment, with arbitrarily dependent increments, into a bound on a terminal weighted event; it drives the tail bounds of the remote-state-preparation analysis.
--
--   **Formalization Note** The supermartingale is stated for the process stopped at $N$, $M_{\min(n,N)}$. The exponential increment is assumed integrable, as the conditional expectation in the hypothesis presupposes. (42) is stated with the lower Lebesgue integral, which needs no integrability side condition.
--
--   Differences from the source:
--   - encoding: E[e^{s(B_n−B_{n−1})−v(D_n−D_{n−1})} | F_{n−1}] ≤ c_n → Bochner conditional expectation bounded a.e. by c_n, with the exponential increment integrable; reason: for a nonnegative variable a finite conditional bound already forces integrability; same hypothesis
--   - encoding: M_n is a nonnegative supermartingale for 0 ≤ n ≤ N → Mathlib Supermartingale of the stopped process M_{min(n,N)} and nonnegativity at every n; reason: the stopped process is the same process on 0 ≤ n ≤ N and constant afterwards; Mathlib's predicate includes adaptedness and integrability
--   - encoding: E[e^{sB_N} 1_A] (42); adapted processes (B_n, D_n)_{n=0}^N; terminal event A → ∫⁻ over A of ofReal(e^{sB_N}); ℕ-indexed processes, strongly F_n-measurable for n ≤ N; A ∈ F_N; reason: the lower integral of a nonnegative function is the expectation; values beyond N are not used
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Lemma 3.18, (42), p.22 (PDF 23)

import Mathlib

set_option autoImplicit false

namespace QSampVerif

open MeasureTheory ProbabilityTheory

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Lemma 3.18 (Exponential supermartingale bound), (42), p.22 (PDF 23).

Let `(B_n, D_n)_{n=0}^N` be adapted real processes with `B₀ = D₀ = 0`, let `s, v ≥ 0` and let
deterministic `c_n > 0` satisfy
`E[e^{s(B_n − B_{n−1}) − v(D_n − D_{n−1})} | F_{n−1}] ≤ c_n` for `1 ≤ n ≤ N`. Then
`M_n = e^{s B_n − v D_n} / ∏_{i=1}^n c_i` is a nonnegative supermartingale (`0 ≤ n ≤ N`), and for
every `h ∈ ℝ` and every terminal event `A ⊆ {D_N ≤ h}`,
`E[e^{s B_N} 1_A] ≤ e^{v h} ∏_{n=1}^N c_n`.

**Formalization Note.** The process `M` lives on `0 ≤ n ≤ N`; it is stated as Mathlib's
`Supermartingale` for the process stopped at `N` (`M_{min(n,N)}`), which includes integrability
and adaptedness. The conditional expectation in the hypothesis presupposes integrability of the
exponential increment, stated as a hypothesis. (42) is stated with the lower Lebesgue integral,
so that it holds without an integrability side condition. -/
theorem lemma_3_18 {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (N : ℕ) (B D : ℕ → Ω → ℝ)
    (hB : ∀ n, n ≤ N → StronglyMeasurable[ℱ n] (B n))
    (hD : ∀ n, n ≤ N → StronglyMeasurable[ℱ n] (D n))
    (hB0 : B 0 = 0) (hD0 : D 0 = 0) (s v : ℝ) (hs : 0 ≤ s) (hv : 0 ≤ v) (c : ℕ → ℝ)
    (hc : ∀ n, 1 ≤ n → n ≤ N → 0 < c n)
    (hint : ∀ n, 1 ≤ n → n ≤ N →
      Integrable (fun ω => Real.exp (s * (B n ω - B (n - 1) ω) - v * (D n ω - D (n - 1) ω))) P)
    (hinc : ∀ n, 1 ≤ n → n ≤ N →
      P[fun ω => Real.exp (s * (B n ω - B (n - 1) ω) - v * (D n ω - D (n - 1) ω)) | ℱ (n - 1)]
        ≤ᵐ[P] fun _ => c n) :
    ((∀ n ω, 0 ≤ Real.exp (s * B (min n N) ω - v * D (min n N) ω) /
        ∏ i ∈ Finset.Icc 1 (min n N), c i) ∧
      Supermartingale (fun n ω => Real.exp (s * B (min n N) ω - v * D (min n N) ω) /
        ∏ i ∈ Finset.Icc 1 (min n N), c i) ℱ P) ∧
    ∀ (h : ℝ) (A : Set Ω), MeasurableSet[ℱ N] A → A ⊆ {ω | D N ω ≤ h} →
      ∫⁻ ω in A, ENNReal.ofReal (Real.exp (s * B N ω)) ∂P ≤
        ENNReal.ofReal (Real.exp (v * h) * ∏ n ∈ Finset.Icc 1 N, c n) := by sorry

end QSampVerif
