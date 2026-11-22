-- Prove2me | Theorems.Thm_TolProdTest_theorem_1_1
-- name    : TolProdTest.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:26:35.380003+00:00
-- url     : https://prove2.me/theorems/69a04716-34f1-4449-bdca-d3b66160eae3
-- title:
--   Theorem 1.1 — fully tolerant product-state tester with $2^{\tilde O((a-b)^{-5})}\log(2/\delta)$ copies and $2^{\tilde O((a-b)^{-5})}n\,\mathrm{poly}(\log(2nd/\delta))$ gates
-- statement:
--   **Problem 1.1.** Let $n\ge1$, $d\ge2$, and fix thresholds $1\ge a>b\ge0$ and a failure probability $\delta\in(0,1/2)$. Given copies of an unknown density operator $\rho$ on $(\mathbb C^d)^{\otimes n}$, promised that $F_{\mathrm{prod}}(\rho)\ge a$ or $F_{\mathrm{prod}}(\rho)\le b$, decide which holds, with success probability at least $1-\delta$.
--
--   **Theorem 1.1.** There is an absolute constant $C>0$ such that for all such $a,b,\delta,n,d$, with $\Delta=a-b$, there is a quantum algorithm, fixed before $\rho$, using
--
--   $$
--   N\ \le\ 2^{\,C\Delta^{-5}\log(e/\Delta)^C}\log\frac2\delta
--   $$
--
--   copies of $\rho$ and at most
--
--   $$
--   2^{\,C\Delta^{-5}\log(e/\Delta)^C}\,n\,\Big(\log\frac{2nd}{\delta}\Big)^C
--   $$
--
--   gates, which accepts every $\rho$ with $F_{\mathrm{prod}}(\rho)\ge a$ with probability at least $1-\delta$ and every $\rho$ with $F_{\mathrm{prod}}(\rho)\le b$ with probability at most $\delta$.
--
--   The number of copies is independent of the number of parties and of the local dimension, even though YES instances may be entangled.
--
--   **Formalization Note** An algorithm is a gate list over $\{H,S,T,X,\mathrm{CNOT}\}$ on $N$ encoded copies of $\rho$ and ancillas in $|0\rangle$; "accept" means answering $F_{\mathrm{prod}}(\rho)\ge a$.
--
--   Differences from the source:
--   - reading: an algorithm (the paper names no computational model); computational complexity → a list of gates over {H, S, T, X, CNOT} (published ShiShallow.Instr) on N encoded copies of ρ plus m ancillas in |0⟩, fixed before ρ; it answers 'F_prod(ρ) ≥ a' iff wire out reads 1 (acceptProbMixed); computational complexity = number of gates; reason: Theorem 3.8 counts quantum gates; a fixed finite universal gate set is the stronger reading (Solovay–Kitaev relates any two at polylog cost); intermediate measurements and the classical threshold are deferred into the circuit
--   - reading: 2^{Õ((a−b)^{−5})} and poly(log(2nd/δ)) → 2^{C Δ^{−5} log(e/Δ)^C} and log(2nd/δ)^C with one absolute C > 0 chosen before a, b, δ, n, d; reason: Õ suppresses polylogarithmic factors (p.8); log(e/Δ) ≥ 1 so the factor does not vanish at Δ = 1; a constant in front of the poly is absorbed into 2^{CΔ^{−5}} ≥ 2^C
--   - encoding: copies of an n-qudit state given to the algorithm → each qudit on Nat.clog 2 d qubit wires, level in little-endian binary, copy j site i on wires (j·n+i)·⌈log₂ d⌉, …; input ρ^{⊗N} = ShadowTomography.UpperBound.tensorPow ρ N; reason: any fixed injective encoding differs by a relabelling of wires, which costs no gates
--   - encoding: ρ ∈ D((ℂ^d)^{⊗n}), n ≥ 1, d ≥ 2 → ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ with WildeQIT.IsDensityOperator ρ (positive semidefinite, trace 1); reason: the computational basis of (ℂ^d)^{⊗n} is indexed by level strings Fin n → Fin d; same operators, sites and levels 0-based
--   - encoding: F_prod(ρ) as a maximum over unit vectors |π_i⟩ ∈ ℂ^d (2) → fprod ρ, the supremum of Re⟨π_1⊗⋯⊗π_n|ρ|π_1⊗⋯⊗π_n⟩ over families of unit vectors; reason: the set is nonempty and bounded and the supremum is attained (compactness); the form is real for Hermitian ρ, so the value is the printed maximum
--   - encoding: 'decide which is the case', success probability ≥ 1 − δ → accept (output 1) means F_prod(ρ) ≥ a: acceptance ≥ 1 − δ on YES, ≤ δ on NO, for every density operator in each promise set; reason: the two error probabilities of a decision procedure
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Theorem 1.1, p.3 (Problem 1.1 and the success requirement, p.2)

import Mathlib
import Definitions.Def_TolProdTest_fprod
import Definitions.Def_TolProdTest_acceptProbMixed
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_tensorPow

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- **Theorem 1.1 (Fully tolerant product-state tester)**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.3: "There is an algorithm that solves Problem 1.1
with probability at least 1 − δ with sample complexity 2^{Õ((a−b)^{−5})} log(2/δ) and computational complexity
2^{Õ((a−b)^{−5})} n poly(log(2nd/δ))."

Problem 1.1 (p.2): "Let n ≥ 1, d ≥ 2, and let the unknown state ρ ∈ D((C^d)^{⊗n}). … Fix thresholds 1 ≥ a > b ≥ 0.
Promised that ρ satisfies either F_prod(ρ) ≥ a or F_prod(ρ) ≤ b, decide which is the case using copies of ρ. … the
algorithms are required to succeed with probability at least 1 − δ, where δ ∈ (0, 1/2) denotes the failure
probability."

There is an absolute constant `C > 0` such that for all `1 ≥ a > b ≥ 0`, `δ ∈ (0, 1/2)`, `n ≥ 1`, `d ≥ 2` there is a
circuit over `{H, S, T, X, CNOT}` on `N` encoded copies of `ρ` and `m` ancillas, fixed before `ρ`, with
`N ≤ 2^{C Δ^{−5} log(e/Δ)^C} log(2/δ)` and at most `2^{C Δ^{−5} log(e/Δ)^C} n log(2nd/δ)^C` gates (`Δ = a − b`),
that accepts every density operator with `F_prod(ρ) ≥ a` with probability at least `1 − δ` and every density
operator with `F_prod(ρ) ≤ b` with probability at most `δ`.

**Formalization Note** The paper names no computational model. An algorithm is a gate list over the published gate
set `ShiShallow.Instr` (`H, S, T, X, CNOT`), acting on `N` copies of `ρ` encoded qudit by qudit
(`Nat.clog 2 d` wires per qudit, little-endian, copy-major) and `m` ancillas in `|0⟩`; it answers "`F_prod(ρ) ≥ a`"
iff wire `out` reads `1` (`acceptProbMixed`); sample complexity is `N`, computational complexity the number of
gates; the circuit may depend on `(a, b, δ, n, d)` but not on `ρ`. `Õ` and `poly` are one absolute constant `C`,
chosen before `a, b, δ, n, d`; `log(e/Δ) ≥ 1` replaces `log(1/Δ)` so the polylogarithmic factor does not vanish at
`Δ = 1`. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ a b δ : ℝ, 0 ≤ b → b < a → a ≤ 1 → 0 < δ → δ < 1 / 2 →
      ∀ n d : ℕ, 1 ≤ n → 2 ≤ d →
      ∃ (N m : ℕ) (out : Fin (N * n * qd d + m)) (gates : List (ShiShallow.Instr (N * n * qd d + m))),
        (N : ℝ) ≤ (2 : ℝ) ^ (C * (a - b) ^ (-5 : ℝ) * Real.log (Real.exp 1 / (a - b)) ^ C) *
            Real.log (2 / δ) ∧
        (gates.length : ℝ) ≤ (2 : ℝ) ^ (C * (a - b) ^ (-5 : ℝ) * Real.log (Real.exp 1 / (a - b)) ^ C) *
            n * Real.log (2 * n * d / δ) ^ C ∧
        ∀ ρ : Matrix (Config n d) (Config n d) ℂ, WildeQIT.IsDensityOperator ρ →
          (a ≤ fprod ρ → 1 - δ ≤ acceptProbMixed (ShadowTomography.UpperBound.tensorPow ρ N) gates out) ∧
          (fprod ρ ≤ b → acceptProbMixed (ShadowTomography.UpperBound.tensorPow ρ N) gates out ≤ δ) := by sorry

end TolProdTest
