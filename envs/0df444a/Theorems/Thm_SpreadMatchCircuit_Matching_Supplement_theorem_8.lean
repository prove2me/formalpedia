-- Prove2me | Theorems.Thm_SpreadMatchCircuit_Matching_Supplement_theorem_8
-- name    : SpreadMatchCircuit.Matching.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:34:24.791357+00:00
-- url     : https://prove2.me/theorems/1ae65081-20ac-41b2-aa3d-3cd1eeede4a4
-- title:
--   Theorem 8 — Monotone circuits for the clique promise problem need size $(n/(kq))^{\Omega(q/\log n)}$
-- statement:
--   There are universal constants $\eta>0$ and $c>0$ such that the following holds for all natural numbers $n,k,q$ with
--   $$\log n<\eta q<k\qquad\text{and}\qquad kq\le \eta n .$$
--   Every monotone Boolean circuit on the $\binom n2$ edge variables that outputs $1$ on every $n$-vertex graph containing a clique of size $k$, and outputs $0$ on every $n$-vertex graph containing no clique of size $q$, has size
--   $$\operatorname{size}(C)\ \ge\ \Bigl(\frac{n}{kq}\Bigr)^{c\,q/\log n}.$$
--
--   The circuits are arbitrary monotone circuits with binary AND and OR gates and unbounded fan-out, with no depth restriction. The theorem gives a lower bound for distinguishing large cliques from graphs of small clique number. Taking $k$ of order $\sqrt n$ and $q=k/2$ gives the bound $\exp(\Omega(\sqrt n/\log n))$. It is a companion result of the mission and is not used in the proof of the matching lower bound.
--
--   **Formalization Note** $\log$ is the natural logarithm. The constants $\eta$ and $c$ are chosen before $n,k,q$ and the circuit, so $\Omega(q/\log n)$ in the exponent becomes $c\,q/\log n$ with a uniform $c$. The size of a circuit counts all of its nodes, input nodes included, as in the mission's circuit model. In the permitted regime $q\ge1$, $k\ge1$ and $n/(kq)\ge 1/\eta$, so the base and the exponent are well defined.
--
--   Differences from the source:
--   - encoding: size (n/(kq))^{Ω(q/log n)} → there is an absolute c > 0, chosen before n, k, q and C, with C.size ≥ (n/(kq))^{c·q/log n}; reason: the asymptotic exponent is read with a uniform constant and no prefactor, which is the literal reading
--   - reading: log unspecified → natural logarithm; reason: ln n ≤ log₂ n, so the hypothesis ln n < ηq admits every instance of the binary-log hypothesis with the same η; a change of base in the exponent is absorbed into c
--   - encoding: circuit size → number of nodes of the published monotone circuit model, input nodes included; reason: the mission's circuit model counts input gates as the source does on p. 11
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 5, Theorem 8; definition of C_S p. 4; proof §4, pp. 14–16

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_MonotoneCircuit
import Definitions.Def_SpreadMatchCircuit_Matching_Supplement_Cliques

namespace SpreadMatchCircuit.Matching.Supplement

/-- Theorem 8, p. 5: if `log n < ηq < k` and `kq ≤ ηn`, every monotone circuit distinguishing
`n`-vertex graphs with a `k`-clique from graphs with no `q`-clique has size at least
`(n/(kq))^{c q / log n}`. The constants `η, c` are absolute and precede every parameter;
`log` is the natural logarithm. -/
theorem theorem_8 :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧
      ∀ (n k q : ℕ), Real.log (n : ℝ) < η * (q : ℝ) → η * (q : ℝ) < (k : ℝ) →
        (k : ℝ) * (q : ℝ) ≤ η * (n : ℝ) →
        ∀ C : MonotoneCircuit (Edge n), DistinguishesCliques C k q →
          ((n : ℝ) / ((k : ℝ) * (q : ℝ))) ^ (c * (q : ℝ) / Real.log (n : ℝ)) ≤
            (C.size : ℝ) := by sorry

end SpreadMatchCircuit.Matching.Supplement
