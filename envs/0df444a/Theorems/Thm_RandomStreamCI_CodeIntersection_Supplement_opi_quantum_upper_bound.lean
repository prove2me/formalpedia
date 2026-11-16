-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_Supplement_opi_quantum_upper_bound
-- name    : RandomStreamCI.CodeIntersection.Supplement.opi_quantum_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:53:07.75644+00:00
-- url     : https://prove2.me/theorems/e126d94d-c3a6-4de2-9db8-60b809fbc5de
-- title:
--   Theorem 29 (companion theorem; not used in the proof of the goal) — DQI quantum streaming algorithm
-- statement:
--   For Problem 2 let $d(n)$ be any admissible degree family with $d(n)\to\infty$ and $d(n)/n\to0$. Put
--   $$\tau(n)=\left\lceil n/2+\sqrt{d(n)n}/8\right\rceil.$$
--   There are $K>0$, a threshold $N$ and nonnegative errors $\varepsilon(n)\to0$ such that, for every admissible $n\ge N$, every characteristic-two field of size $q=n+1$ and every enumeration of its nonzero points, there is one legal polynomial-output quantum streaming program $Q$ satisfying
--   $$\mathrm{memory}(Q)\le Kd(n)\log_2 n,\qquad\forall\pi,\quad\Pr_{H,\mathrm{quantum\ outcomes}}[\mathrm{score}(Q)\ge\tau(n)\mid\pi]\ge1-\varepsilon(n).$$
--   The program and common error bound precede the order quantifier. The output is an actual polynomial of degree below $d(n)$, including zero, or failure; abort probability is retained in the unconditional success law. All persistent classical and quantum registers, reusable channel environments, decoding scratch and final coefficient readout are charged. No polynomial-time claim is made. This companion theorem has the full quantum degree regime, independently of Theorem 27's stronger classical assumptions.
--
--   Differences from the source:
--   - encoding: coordinates, times and symbols as finite labelled sets → Fin indices numbered from zero and finite alphabet types; reason: bijections of labels preserve every source instance
--   - encoding: q any power of two, n=q-1 and distinct nonzero evaluation points → every finite field of characteristic two with cardinality n+1 and every nonzero embedding Fin n into it; reason: all finite fields and evaluation enumerations in Problem 2 are covered, including non-prime fields
--   - encoding: asymptotics along source-admissible n and unspecified eventual constants → the filter atTop restricted to all n+1=2^e, and explicit positive constants and thresholds; reason: expands the asymptotic quantifiers without selecting a smaller subsequence
--   - reading: one-pass quantum streaming with bounded space and unrestricted computation time → fixed finite-dimensional current-item-controlled CPTP channels and an input-independent normalized coefficient-output POVM; reason: the source specifies no uniform circuit convention; all persistent registers, recycled dilation environments, preparation and output workspace are charged, and arbitrary fixed operations require no extra input access
--   - encoding: output a polynomial in P_d with unconditional success probability → a normalized POVM over d coefficient values or an explicit abort, averaged over the uniform oracle at each fixed order; reason: the published coefficient polynomial bijects d coefficients with P_d, and aborts are never postselected away
--   - encoding: O(d log n) total quantum workspace → 3q persistent-and-dilation space plus twice the ceiling of log_2(1+|F|^d) and one flag, bounded by K*d*log_2 n; reason: this charges every register and uses coefficient outputs; the constant-factor overhead preserves the full asymptotic bound
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, release papers-1/71.pdf, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Theorem 29, p. 28 (printed = PDF; offset 0)

import Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_Asymptotics
import Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_Quantum

namespace RandomStreamCI.CodeIntersection.Supplement

open Filter Topology

/-- Theorem 29, pp. 28--30. The quantum degree regime is deliberately distinct from
Theorem 27's. One actual polynomial-output program serves every stream order. -/
theorem opi_quantum_upper_bound (d : ℕ → ℕ) (hd : DegreeFamily d)
    (hlarge : Tendsto (fun n => (d n : ℝ)) opiAtTop Filter.atTop)
    (hsmall : Tendsto (fun n => (d n : ℝ) / (n : ℝ)) opiAtTop (𝓝 0)) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∃ ε : ℕ → ℝ,
      (∀ n, 0 ≤ ε n) ∧ Tendsto ε opiAtTop (𝓝 0) ∧
      ∀ n : ℕ, N ≤ n → ∀ hn : AdmissibleLength n,
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2],
      Fintype.card F = n + 1 → ∀ α : Fin n ↪ F, (∀ i, α i ≠ 0) →
      ∃ Q : PolynomialProgram n (d n) F,
        (Q.memoryBits : ℝ) ≤ K * (d n : ℝ) * log₂ (n : ℝ) ∧
        ∀ π : Order n F, 1 - ε n ≤ Q.successAtOrder α (target n (d n)) π := by sorry

end RandomStreamCI.CodeIntersection.Supplement
