-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_corollary_5_5
-- name    : QuantumStateIdentity321.Schur.Supplement.corollary_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:02:35.374423+00:00
-- url     : https://prove2.me/theorems/322a82bb-3e79-484f-83f1-35f93b3d8259
-- title:
--   Corollary 5.5 — any algorithm for Problem 2 with error $\delta<1/2$ needs $m\ge\log(1+4n(1-2\delta)^2)/\log\eta$
-- statement:
--   Let $n\ge1$, $p\in(0,1)\setminus\{1/2\}$ and $0<\delta<1/2$, and set $\eta=\frac1{p(1-p)}-3$. Then $\eta>1$, and every algorithm that solves Problem 2 with probability at least $1-\delta$ (it accepts the yes case $(X_1,\dots,X_n)$ with probability at least $1-\delta$ and the no case $(Z_1,\dots,Z_n)$ with probability at most $\delta$) requires
--
--   $$
--   m\ge\frac{\log\bigl(1+4n(1-2\delta)^2\bigr)}{\log\eta}.
--   $$
--
--   Combined with Theorem 5.2 this yields the lower bound $\Omega(\log(n/\delta)/\log(1/\varepsilon))$ of Theorem 5.6.
--
--   **Formalization Note** An algorithm for Problem 2 may be randomized; it is given by its acceptance probability $f(x)\in[0,1]$ on the observed counts $x\in\{0,\dots,m\}^n$.
--
--   Differences from the source:
--   - generalization: n ≥ 2 (standing assumption of the paper) → n ≥ 1; reason: the statement needs only a nonempty [n]; it specializes to every n ≥ 2
--   - encoding: an algorithm for Problem 2 → a test f : (Fin n → Fin (m+1)) → [0, 1] (acceptance probability); reason: every randomized classical algorithm on the counts is such a test
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Corollary 5.5, PDF/printed p.22, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_LowerBound

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

/-- Corollary 5.5, p.22: for `p ∈ (0, 1) ∖ {1/2}` and `0 < δ < 1/2`, `η = 1/(p(1 − p)) − 3 > 1`,
and every algorithm that solves Problem 2 with probability at least `1 − δ` requires
`m ≥ log(1 + 4n(1 − 2δ)²)/log η`. -/
theorem corollary_5_5 (n m : ℕ) (hn : 0 < n) (p δ : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hp : p ≠ 1 / 2) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    1 < 1 / (p * (1 - p)) - 3 ∧
      ∀ f : (Fin n → Fin (m + 1)) → ℝ, SolvesProblem2 f p δ →
        Real.log (1 + 4 * (n : ℝ) * (1 - 2 * δ) ^ 2) / Real.log (1 / (p * (1 - p)) - 3) ≤
          (m : ℝ) := by sorry

end QuantumStateIdentity321.Schur.Supplement
