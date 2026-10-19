-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL23_onlineThresholdSearch_sampleBound
-- name    : QAlgorithms.Papers.RoadmapL23.onlineThresholdSearch_sampleBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:21:47.154385+00:00
-- url     : https://prove2.me/theorems/5d4dffcf-3326-424c-a2b9-0e7bfba9e572
-- title:
--   Online quantum Threshold Search with a dimension-independent copy bound
-- statement:
--   There are a universal constant $C>0$ and a copy-count function $n_{\mathrm{TS}}(m,\varepsilon,\delta)$, depending only on the number of tests $m$ and the accuracy and failure parameters $\varepsilon,\delta$, with the following property. For every integer $m\ge1$ and every $0<\varepsilon,\delta<1/2$, write $L=\log(1/\delta)$. Then
--   $$
--   n_{\mathrm{TS}}(m,\varepsilon,\delta)
--   \le \left\lceil C\,\frac{((\log m)^2+L)L}{\varepsilon^2}\right\rceil.
--   $$
--
--   For every dimension $d\ge1$, there is an online quantum protocol that begins with $n_{\mathrm{TS}}(m,\varepsilon,\delta)$ independent, unentangled copies of an unknown state $\rho\in\mathbb C^{d\times d}$, where $\rho$ is positive semidefinite and $\operatorname{tr}\rho=1$, together with a known ancillary state. Observable/threshold pairs $(A_t,\theta_t)$ are then presented in order, with $0\le A_t\le I$ and $\theta_t\in[0,1]$. The protocol is fixed independently of $\rho$ and the stream, and its decision at stage $t$ depends only on the presented prefix and its retained quantum memory. It either passes or halts and selects the current index $t$. Selection asserts $\operatorname{tr}(\rho A_t)>\theta_t-\varepsilon$; after $m$ passes it asserts $\operatorname{tr}(\rho A_i)\le\theta_i$ for all $i$.
--
--   For every such state and stream,
--   $$
--   \Pr\!\left[
--   \begin{array}{l}
--   \text{the protocol selects }t\text{ with }\operatorname{tr}(\rho A_t)>\theta_t-\varepsilon,\\
--   \text{or passes on all }m\text{ pairs with }\operatorname{tr}(\rho A_i)\le\theta_i\text{ for every }i
--   \end{array}
--   \right]\ge1-\delta.
--   $$
--   The stream may depend on preceding public pass responses. No promise that an expectation exceeds a threshold is required. Both kinds of claim are valid in the overlap $\theta_t-\varepsilon<\operatorname{tr}(\rho A_t)\le\theta_t$.
--
--   This theorem bounds the sample cost of online search among quantum observables independently of the state dimension.
--
--   **Formalization Note** Natural logarithms and a ceiling express the source's uniform big-O copy bound. Physical Kraus instruments act on the initial tensor power of $\rho$ and an ancillary state; the model uses only copy access. The selected index is zero-based in Lean.
-- source:
--   Improved quantum data analysis, arXiv:2011.10908v4, Theorem 1.1, PDF p. 3. https://arxiv.org/abs/2011.10908v4 . PDF SHA-256: 108fed18d680b4156f8b6115241146406f0d53d385b1a0fc61277ef26d6749e6.

import Definitions.Def_QAlgorithms_Defs_OnlineThresholdSearch
set_option autoImplicit false

namespace QAlgorithms.Papers.RoadmapL23

/-- Badescu and O'Donnell, *Improved quantum data analysis*, arXiv:2011.10908v4,
Theorem 1.1 (PDF p.3; standing assumptions pp.2-3 and 8-10, reductions pp.19-21).
There is a dimension-independent copy count bounded by
`O(((log m)^2 + log(1/delta)) * log(1/delta) / eps^2)` and an online protocol
whose final claim is correct with probability at least `1 - delta`.
The protocol starts with a single batch of independent copies. Each stage sees only
the observable/threshold prefix, passes or selects that stage, and after all passes
claims every expectation is at most its threshold. Selection uses the strict
inequality `expectation > threshold - eps`; no existence promise is assumed. -/
theorem onlineThresholdSearch_sampleBound :
    ∃ C : ℝ, 0 < C ∧ ∃ nTS : ℕ → ℝ → ℝ → ℕ,
      ∀ m : ℕ, 1 ≤ m → ∀ eps delta : ℝ,
        0 < eps → eps < 1 / 2 → 0 < delta → delta < 1 / 2 →
        nTS m eps delta ≤
          ⌈C * ((Real.log (m : ℝ)) ^ 2 + Real.log (1 / delta)) *
            Real.log (1 / delta) / eps ^ 2⌉₊ ∧
        ∀ d : ℕ, 1 ≤ d →
          ∃ P : QAlgorithms.ThresholdSearch.OnlineProtocol d m (nTS m eps delta),
            QAlgorithms.ThresholdSearch.IsCorrect P eps delta := by sorry

end QAlgorithms.Papers.RoadmapL23
