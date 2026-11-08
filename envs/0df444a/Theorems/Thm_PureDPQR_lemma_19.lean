-- Prove2me | Theorems.Thm_PureDPQR_lemma_19
-- name    : PureDPQR.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:59:24.335215+00:00
-- url     : https://prove2.me/theorems/aa5fd458-611f-4fb1-b636-6462a5ec7487
-- title:
--   Lemma 19, p.21 — deterministic MW progress $\sum_t\langle H_t-h,s_{i_t}\rangle\le N(\log d/\rho+\rho T)$
-- statement:
--   **Lemma 19** (Deterministic MW progress). Let $N,T\ge1$, $0<\rho\le\frac12$, and let $s_1,\dots,s_K$ have entries in $[-1,1]$. For every transcript $(i_1,\dots,i_T)$ and every histogram $h$ of mass $N$, the candidate histograms $H_t=Np_t$ of Algorithm 1 satisfy
--
--   $$\sum_{t=1}^T\langle H_t-h,s_{i_t}\rangle\le N\Big(\frac{\log d}{\rho}+\rho T\Big).$$
--
--   This is the multiplicative-weights regret bound used in Proposition 21; it holds for every label sequence, however generated.
--
--   **Formalization Note** $H_t$ is `N • iterate ρ s y t` for the 0-based round $t$; $h\in H_{N,d}$ is cast to $\mathbb R^d$.
--
--   Differences from the source:
--   - generalization: the signed list of a table in [0,1]^{k×d} → any s : Fin K → Fin d → ℝ with |s_a(j)| ≤ 1; reason: the proof uses only s_t(j) ∈ [−1, 1] (p.21); the signed list is such an s
--   - encoding: 1-based rounds and labels → Fin T, Fin K; reason: Lean convention
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Lemma 19, p.21 (PDF p.22); Algorithm 1, p.19

import Mathlib
import Definitions.Def_PureDPQR_IsDP
import Definitions.Def_PureDPQR_transcriptProb

namespace PureDPQR

/-- **Lemma 19** (Deterministic MW progress), p.21 (PDF p.22).

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…).

"For every transcript (i_1, · · · , i_T) and every histogram h of mass N,
∑_{t=1}^T ⟨H_t − h, s_{i_t}⟩ ≤ N (log d/ρ + ρT). (5.8)"

Here `H_t = N p_t` are the candidate histograms of Algorithm 1 (p.19) under its Require line
(`N, T ≥ 1`, `0 < ρ ≤ 1/2`); `λ` does not enter.

**Formalization Note.** The signed list is any `s : Fin K → Fin d → ℝ` with entries in `[−1, 1]`
(the property the proof uses, p.21); the signed list of a query table in `[0,1]^{k×d}` is one (a
generalization). `H_t` for 0-based round `t` is `N • iterate ρ s y t`; the histogram `h` is in
`H_{N,d}` and is cast to `ℝ^d`. -/
theorem lemma_19 {K d T : ℕ} (N : ℕ) (ρ : ℝ) (s : Fin K → Fin d → ℝ) (hN : 1 ≤ N)
    (hT : 1 ≤ T) (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 2) (hs : ∀ a j, |s a j| ≤ 1)
    (y : Fin T → Fin K) (h : Fin d → ℕ) (hh : h ∈ histograms N d) :
    ∑ t : Fin T, dot ((N : ℝ) • iterate ρ s y t - fun j => (h j : ℝ)) (s (y t)) ≤
      (N : ℝ) * (Real.log d / ρ + ρ * T) := by sorry

end PureDPQR
