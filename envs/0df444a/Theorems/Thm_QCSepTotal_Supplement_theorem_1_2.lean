-- Prove2me | Theorems.Thm_QCSepTotal_Supplement_theorem_1_2
-- name    : QCSepTotal.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:31:59.818087+00:00
-- url     : https://prove2.me/theorems/a34c845b-2f3c-440a-9f42-bb0e00fc9d06
-- title:
--   Theorem 1.2 — a total function with $Q_2(f)=\mathrm{polylog}(n)$ and $R(f)=\tilde\Omega(\sqrt n)$
-- statement:
--   There is a total function $f:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}$ with
--   $$Q_2(f)=\mathrm{polylog}(n)\qquad\text{and}\qquad R(f)=\tilde\Omega(\sqrt n).$$
--
--   Here $Q_2(f)$ is the least number of qubits exchanged by a quantum protocol without prior entanglement that uses at most two messages and computes $f$ with error at most $1/3$ on every input, and $R(f)$ is the public-coin randomized communication complexity of $f$ at error $1/3$. Explicitly: there is a constant $K$ such that for every input length $n\ge2$ there is a total $f$ on $n$-bit inputs per party with
--   $$Q_2(f)\le K(\log_2 n)^K\qquad\text{and}\qquad \sqrt n\le K(\log_2 n)^K\,R(f).$$
--
--   This improves the exponent $1/6$ of Gavinsky's separation for total functions to $1/2$, with only two quantum messages. The theorem is unconditional.
--
--   **Formalization Note** $\mathrm{polylog}(n)=(\log n)^{O(1)}$ and $\tilde\Omega$ suppresses factors polynomial in $\log n$ (footnote 1, p.1; logarithms binary, p.3); one constant $K$ is chosen before $n$. The models are the base mission's: $Q_r(f)\le q$ is `HasQProtocol (total f) r q` and $R$ is `R`.
--
--   Differences from the source:
--   - reading: polylog(n) and Ω̃(√n) → explicit factors K (log₂ n)^K with one K chosen before n; reason: footnote 1, p.1: the notation suppresses factors polynomial in log n
--   - reading: a family of total functions, one for each (large) n → every n ≥ 2; reason: for bounded n a function such as f(x, y) = x₁ has Q₂ ≤ 1 and R ≥ 1, so the constant absorbs the small cases; n ≥ 2 keeps log₂ n > 0
--   - encoding: R(·) and Q₂(·) of p.5 → the published base-mission models R and HasQProtocol (at most 2 messages, owned-qubit unitary model, transcript-determined classical output); reason: the same models used by the mission's goal; the differences are absorbed by the constant K, as recorded on QCSepTotal.theorem_1_4
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), Theorem 1.2, p.2 (proof p.14)

import Mathlib
import Definitions.Def_QCSepTotal_RandProtocol
import Definitions.Def_QCSepTotal_QProtocol

namespace QCSepTotal.Supplement

/-- **Theorem 1.2** (F. Le Gall, *Improved Separations between Quantum and Classical
Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…),
p.2; proved on p.14). There is a total function `f : {0,1}ⁿ × {0,1}ⁿ → {0,1}` with
`Q₂(f) = polylog(n)` and `R(f) = Ω̃(√n)`.

**Formalization Note.** `polylog(n)` is `(log n)^{O(1)}` and `Ω̃` suppresses factors polynomial in
`log n` (footnote 1, p.1; logarithms are binary, p.3): one constant `K`, chosen before `n`, with
`Q₂(f) ≤ K (log₂ n)^K` and `√n ≤ K (log₂ n)^K R(f)`, for every input length `n ≥ 2` (for bounded
`n` the constant absorbs everything; `n ≥ 2` keeps `log₂ n > 0`). `Q₂(f) ≤ q` is `HasQProtocol
(total f) 2 q`: a quantum protocol without prior entanglement, with at most two messages, cost at
most `q` qubits and error at most `1/3` on every input. `R` is the public-coin randomized
complexity at error `1/3` of the base mission. The theorem is unconditional: Gavinsky's bounds on
`Shape_m` and Harvey–van der Hoeven's multiplication circuit are proof ingredients, not
hypotheses. -/
theorem theorem_1_2 :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n → ∃ f : (Fin n → Bool) → (Fin n → Bool) → Bool,
      HasQProtocol (total f) 2 ⌊(K : ℝ) * Real.logb 2 n ^ K⌋₊ ∧
      Real.sqrt n ≤ K * Real.logb 2 n ^ K * R (total f) := by sorry

end QCSepTotal.Supplement
