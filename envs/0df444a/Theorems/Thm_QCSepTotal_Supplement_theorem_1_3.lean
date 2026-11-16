-- Prove2me | Theorems.Thm_QCSepTotal_Supplement_theorem_1_3
-- name    : QCSepTotal.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:32:38.924087+00:00
-- url     : https://prove2.me/theorems/0fbc91b2-e82f-4eac-b95b-b9a1bf2741c2
-- title:
--   Theorem 1.3 — for each $k\ge2$, a total function with $Q_{2\lceil k/2\rceil+1}(f)=\mathrm{polylog}(n)$ and $R(f)=\tilde\Omega(n^{1-1/k})$
-- statement:
--   For every constant integer $k\ge2$, there is a total function $f:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}$ with
--   $$Q_{2\lceil k/2\rceil+1}(f)=\mathrm{polylog}(n)\qquad\text{and}\qquad R(f)=\tilde\Omega\bigl(n^{1-1/k}\bigr).$$
--
--   Here $Q_r(f)$ is the least number of qubits exchanged by a quantum protocol without prior entanglement that uses at most $r$ messages and computes $f$ with error at most $1/3$ on every input, and $R(f)$ is the public-coin randomized communication complexity of $f$ at error $1/3$. Explicitly: for every integer $k\ge2$ there is a constant $K$ (depending on $k$) such that for every input length $n\ge2$ there is a total $f$ on $n$-bit inputs per party with
--   $$Q_{2\lceil k/2\rceil+1}(f)\le K(\log_2 n)^K\qquad\text{and}\qquad n^{1-1/k}\le K(\log_2 n)^K\,R(f).$$
--
--   Thus every exponent below $1$ is achieved with a constant number of quantum messages. The theorem is unconditional.
--
--   **Formalization Note** $\tilde\Omega$ and $\mathrm{polylog}$ suppress factors polynomial in $\log n$ (footnote 1, p.1; logarithms binary, p.3); since $k$ is a constant, $K$ is chosen after $k$ and before $n$. $\lceil k/2\rceil$ is the natural-number quotient $(k+1)/2$ and $n^{1-1/k}$ is a real power. The models are the base mission's: $Q_r(f)\le q$ is `HasQProtocol (total f) r q` and $R$ is `R`.
--
--   Differences from the source:
--   - reading: polylog(n) and Ω̃(n^{1−1/k}) for a constant k → explicit factors K (log₂ n)^K with K chosen after k and before n; reason: footnote 1, p.1: the notation suppresses factors polynomial in log n, and the constant may depend on the fixed k
--   - reading: a family of total functions, one for each (large) n → every n ≥ 2; reason: for bounded n a function such as f(x, y) = x₁ has Q_r ≤ 1 and R ≥ 1, so the constant absorbs the small cases; n ≥ 2 keeps log₂ n > 0
--   - encoding: ⌈k/2⌉ → (k + 1) / 2 in ℕ; reason: equal for every natural k
--   - encoding: R(·) and Q_{2⌈k/2⌉+1}(·) of p.5 → the published base-mission models R and HasQProtocol (at most 2⌈k/2⌉+1 messages, owned-qubit unitary model, transcript-determined classical output); reason: the same models used by the mission's goal; the differences are absorbed by the constant K, as recorded on QCSepTotal.theorem_1_4
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), Theorem 1.3, p.2 (proof p.15)

import Mathlib
import Definitions.Def_QCSepTotal_RandProtocol
import Definitions.Def_QCSepTotal_QProtocol

namespace QCSepTotal.Supplement

/-- **Theorem 1.3** (F. Le Gall, *Improved Separations between Quantum and Classical
Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…),
p.2; proved on p.15). For every constant integer `k ≥ 2`, there is a total function
`f : {0,1}ⁿ × {0,1}ⁿ → {0,1}` with `Q_{2⌈k/2⌉+1}(f) = polylog(n)` and `R(f) = Ω̃(n^{1−1/k})`.

**Formalization Note.** `k` is a constant, so the constant `K` is chosen after `k` and before
`n`: `Q_{2⌈k/2⌉+1}(f) ≤ K (log₂ n)^K` and `n^{1−1/k} ≤ K (log₂ n)^K R(f)` for every input length
`n ≥ 2` (footnote 1, p.1; binary logarithms, p.3). `⌈k/2⌉` is `(k + 1) / 2` in `ℕ`; the
exponent `1 − 1/k` is a real power. `Q_r(f) ≤ q` is `HasQProtocol (total f) r q` (at most `r`
messages, no prior entanglement, error at most `1/3`); `R` is the public-coin randomized
complexity at error `1/3` of the base mission. The theorem is unconditional: the Bansal–Sinha
bound, IP lifting and the quantum algorithm it cites are proof ingredients, not hypotheses. -/
theorem theorem_1_3 :
    ∀ k : ℕ, 2 ≤ k → ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n → ∃ f : (Fin n → Bool) → (Fin n → Bool) → Bool,
      HasQProtocol (total f) (2 * ((k + 1) / 2) + 1) ⌊(K : ℝ) * Real.logb 2 n ^ K⌋₊ ∧
      (n : ℝ) ^ (1 - 1 / (k : ℝ)) ≤ K * Real.logb 2 n ^ K * R (total f) := by sorry

end QCSepTotal.Supplement
