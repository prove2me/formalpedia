-- Prove2me | Theorems.Thm_QLocalCert_Supplement_theorem_21
-- name    : QLocalCert.Supplement.theorem_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:41:07.969876+00:00
-- url     : https://prove2.me/theorems/7ed67402-a8ba-41f1-beeb-ebbefe3f33c0
-- title:
--   Theorem 21 — quantum lower bound for equality on a path: $q_\partial=\Omega(\log N)$, and $\Omega(\log N)$ certificate qubits near the endpoint for $r\ge3$
-- statement:
--   Fix a completeness $c$ and a soundness error $s$ with $0\le s<c\le1$ and $\delta=2c-1-s>0$. There are a constant $C>0$ and a threshold $N_0$ (depending only on $c,s$) such that for every $N\ge N_0$, every path length $r\ge2$ and every one-round dQMA protocol for $\mathrm{EQ}^2_N$ on the path $v_0,\dots,v_r$ (Definition 18) with completeness $c$ and soundness $s$:
--
--   1. the boundary cost satisfies
--   $$
--   q_\partial=c(v_{r-1})+c(v_r)+m(v_{r-2},v_{r-1})\ \ge\ C\log_2 N;
--   $$
--   2. if $r\ge3$, then, whatever the message sizes,
--   $$
--   c(v_{r-2})+c(v_{r-1})+c(v_r)\ \ge\ C\log_2 N .
--   $$
--
--   In particular some node receives $\Omega(\log N)$ certificate qubits even with arbitrarily entangled certificates and unrestricted messages (Theorem 6). The restriction $r\ge3$ in the second part is necessary: for $r=2$ the endpoints can send their strings to the middle node.
--
--   **Formalization Note** The constants are chosen after $c,s$ and before $N$, $r$ and the protocol, so they are uniform in the path length and all register and message sizes. Logarithms are base 2.
--
--   Differences from the source:
--   - reading: Ω(log N) for fixed c, s → C(c, s) > 0 and N₀(c, s), uniform in r and in all register and message sizes; reason: the proof gives Ω_δ(log N) from a packing bound depending only on δ (p.33), and the statement says "independently of the message sizes"
--   - encoding: completeness c and soundness error s → hypotheses 0 ≤ s < c ≤ 1 and s < 2c − 1; reason: 0 ≤ s < c ≤ 1 is the model's standing assumption (Definition 7, p.16)
--   - encoding: arbitrary pure prover state (Definition 18) → arbitrary density operator; reason: by convexity the honest and worst-case acceptance probabilities are the same
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Theorem 21, p.33 (= Theorem 6, p.6); Definition 18 and q∂, p.32

import Mathlib
import Definitions.Def_QLocalCert_Supplement_PathDQMA

set_option autoImplicit false

namespace QLocalCert.Supplement

/-- **Theorem 21** (p.33; its second assertion is Theorem 6, p.6). "Any one-round dQMA protocol for
EQ²_N on a path of length r ≥ 2 with fixed completeness c and soundness error s satisfying
δ = 2c − 1 − s > 0 has q∂ ≥ Ω(log N). Moreover, if r ≥ 3, then c(v_{r−2}) + c(v_{r−1}) + c(v_r) =
Ω(log N), independently of the message sizes."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Theorem 21, p.33; Definition 18 and
`q∂ := c(v_{r−1}) + c(v_r) + m(v_{r−2}, v_{r−1})`, p.32; Theorem 6, p.6.

**Formalization Note.**
* The model is `PathDQMA N r` (Definition 18); `q∂` is `PathDQMA.qBoundary`.
* "Fixed c, s": the constant `C > 0` and the threshold `N₀` are chosen after `c, s` (the proof gives
  `Ω_δ`) and before `N`, the path length `r` and the protocol, so they are uniform in `r` and in all
  register and message sizes. The model's `0 ≤ s < c ≤ 1` (Definition 7, p.16) is assumed together
  with `2c − 1 > s`.
* `log` is `Real.logb 2`. -/
theorem theorem_21 :
    ∀ c s : ℝ, 0 ≤ s → s < c → c ≤ 1 → s < 2 * c - 1 →
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℕ, 2 ≤ r → ∀ P : PathDQMA N r,
        P.Correct c s →
          C * Real.logb 2 N ≤ (P.qBoundary : ℝ) ∧
          (3 ≤ r → C * Real.logb 2 N ≤ ((P.cert (r - 2) + P.cert (r - 1) + P.cert r : ℕ) : ℝ)) := by sorry

end QLocalCert.Supplement
