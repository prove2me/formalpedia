-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_25_5_3
-- name    : WildeQIT.Compression.Supplement.theorem_25_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:24:45.037992+00:00
-- url     : https://prove2.me/theorems/d01360e8-a02f-4348-aeca-cc536dffd739
-- title:
--   Theorem 25.5.3: the quantum dynamic capacity region of the qudit erasure channel
-- statement:
--   Let $\mathcal N^\varepsilon(\rho)=(1-\varepsilon)\rho+\varepsilon|e\rangle\langle e|$ be the quantum erasure channel on a $d$-dimensional input, with an erasure flag $|e\rangle$ orthogonal to the input space and $\varepsilon\in[0,1]$. For $\lambda\in[0,1]$ let $R_\lambda$ be the set of rate triples $(C,Q,E)$ with
--
--   $$
--   C+2Q\le(1-\varepsilon)(1+\lambda)\log d,\qquad Q+E\le(1-2\varepsilon)\lambda\log d,\qquad C+Q+E\le(1-\varepsilon-\varepsilon\lambda)\log d .
--   $$
--
--   1. If $\varepsilon\in[0,\frac12]$, the quantum dynamic capacity region is $\mathcal C_{CQE}(\mathcal N^\varepsilon)=\bigcup_{\lambda\in[0,1]}R_\lambda$.
--   2. If $\varepsilon\in(\frac12,1]$, the region $\bigcup_{\lambda\in[0,1]}R_\lambda$ is achievable: it is contained in $\mathcal C_{CQE}(\mathcal N^\varepsilon)$.
--
--   The region shows that time sharing is an optimal strategy for the erasure channel.
--
--   **Formalization Note** $\mathcal N^\varepsilon$ is the published `WildeQIT.ErasureClassical.erasureChannel` (input `Fin d`, output `Option (Fin d)`), used through its action; $\mathcal C_{CQE}$ is `operationalDynamicRegion` of the published `Claimed50.P20`. Logarithms are base 2.
--
--   Differences from the source:
--   - encoding: a d-dimensional input → `0 < d`; reason: a zero-dimensional input carries no state; the hypothesis excludes only that case
--   - encoding: C_CQE(N) is the union of all achievable rate triples (p. 696) → operationalDynamicRegion of Claimed50.P20 (the closure of the achievable triples); reason: the region of the referenced Theorem 25.2.1; the set of achievable triples is closed, so the two agree
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 25.5.3, p. 719; eq. (25.151), p. 718

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20
import Definitions.Def_WildeQIT_ErasureClassical_erasureChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 25.5.3, p. 719.
-/

namespace WildeQIT.Compression.Supplement

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P20

/-- **Theorem 25.5.3** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 719): "Let `N^ε` be a quantum erasure channel with
`ε ∈ [0, 1/2]`. Then the quantum dynamic capacity region `C_CQE(N^ε)` is equal to the union of the
following regions, obtained by varying `λ ∈ [0, 1]`: `C + 2Q ≤ (1 − ε)(1 + λ) log d`,
`Q + E ≤ (1 − 2ε) λ log d`, `C + Q + E ≤ (1 − ε − ελ) log d`. The region is achievable for
`ε ∈ (1/2, 1]`."

Formalization Note: both claims are asserted: equality for `ε ≤ 1/2`, and containment of the same
union in `C_CQE(N^ε)` for `ε > 1/2`. `N^ε` is the published d-dimensional erasure channel
`WildeQIT.ErasureClassical.erasureChannel d ε` ((25.151): input `Fin d`, output `Option (Fin d)`,
dimension `d + 1`), as a superoperator through its action `QChannel.apply`; `C_CQE` is
`operationalDynamicRegion` of the published `Claimed50.P20`, and `rateConstraints b r` is the
triple of inequalities `C + 2Q ≤ b₀`, `Q + E ≤ b₁`, `C + Q + E ≤ b₂` for `r = (C, Q, E)`.
`d ≥ 1`; logarithms are base 2. -/
theorem theorem_25_5_3 (d : ℕ) (hd : 0 < d) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (ε ≤ 1 / 2 →
      operationalDynamicRegion (WildeQIT.ErasureClassical.erasureChannel d ε h0 h1).apply =
        ⋃ t ∈ Set.Icc (0 : ℝ) 1, {r : Rate | rateConstraints
          ![(1 - ε) * (1 + t) * Real.logb 2 d, (1 - 2 * ε) * t * Real.logb 2 d,
            (1 - ε - ε * t) * Real.logb 2 d] r}) ∧
    (1 / 2 < ε →
      (⋃ t ∈ Set.Icc (0 : ℝ) 1, {r : Rate | rateConstraints
          ![(1 - ε) * (1 + t) * Real.logb 2 d, (1 - 2 * ε) * t * Real.logb 2 d,
            (1 - ε - ε * t) * Real.logb 2 d] r}) ⊆
        operationalDynamicRegion (WildeQIT.ErasureClassical.erasureChannel d ε h0 h1).apply) := by sorry

end WildeQIT.Compression.Supplement
