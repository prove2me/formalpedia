-- Prove2me | Theorems.Thm_SquashedKey_eq_21_cmi_continuity
-- name    : SquashedKey.eq_21_cmi_continuity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:30:00.621117+00:00
-- url     : https://prove2.me/theorems/9fe8f046-1fac-47ce-9c2b-42ebd23b1ef4
-- title:
--   Eq. (21) [Shi17] — $|I(A;B|E)_\rho-I(A;B|E)_\omega|\le 2\varepsilon\log_2\min\{\dim H_A,\dim H_B\}+2(1+\varepsilon)h_2(\varepsilon/[1+\varepsilon])$
-- statement:
--   Let $A$, $B$, $E$ be quantum systems, $\rho_{ABE},\omega_{ABE}$ states and $\varepsilon\in[0,1]$ with $\tfrac12\|\rho_{ABE}-\omega_{ABE}\|_1\le\varepsilon$. Write
--   $$
--   c(d)=2\varepsilon\log_2 d+2(1+\varepsilon)\,h_2\!\left(\frac{\varepsilon}{1+\varepsilon}\right)\qquad(=f_1(\varepsilon,d)).
--   $$
--
--   1. If $A$ is finite-dimensional, then $\bigl|I(A;B|E)_\rho-I(A;B|E)_\omega\bigr|\le c(\dim H_A)$.
--   2. If $B$ is finite-dimensional, then $\bigl|I(A;B|E)_\rho-I(A;B|E)_\omega\bigr|\le c(\dim H_B)$.
--
--   The other system and $E$ may be infinite-dimensional. Together the two clauses are the bound with $\min\{\dim H_A,\dim H_B\}$ of the display. Theorem 2 uses clause 1 for $I(A;BB'|E)$ and clause 2 for $I(A';B|AB'E)$, the key systems having dimension $K$.
--
--   **Formalization Note** $I$ is the extended conditional mutual information in bits, in $[0,+\infty]$; each absolute value is written as two one-sided inequalities, and $\dim H_A$ is the cardinality of the finite index type.
--
--   Differences from the source:
--
--   - reading: I(A;B|E) = H(AE)+H(BE)−H(E)−H(ABE) (15), which is ∞ − ∞ when the entropies are infinite → Shirokov's extended conditional mutual information (published qcmi: supremum over finite-rank projectors P on A of I(PA;BE) − I(PA;E)) divided by ln 2, valued in ℝ≥0∞; reason: the paper allows infinite-dimensional shields and extensions and takes (21) from [Shi17], which is proved for this quantity; it equals (15) whenever the entropies in (15) are finite, so it changes no instance on which (15) is defined
--   - encoding: Hilbert spaces of any dimension → ℓ²(I) for an arbitrary index type I (no finiteness or countability), operators as coefficient arrays, states as the published trace-class State I; reason: every Hilbert space has an orthonormal basis and is ℓ² of its index set; the same instances
--   - encoding: one bound with min{dim(H_A), dim(H_B)} → two clauses: under Finite A with |A|, and under Finite B with |B|; reason: when both are finite the clause with the smaller dimension is the display; when one is finite the minimum is its dimension; when neither is finite the right-hand side is infinite (for ε = 0 the states coincide) and there is nothing to state
--   - encoding: |I_ρ − I_ω| ≤ c → I_ρ ≤ I_ω + c and I_ω ≤ I_ρ + c in ℝ≥0∞; reason: no ∞ − ∞; equivalent whenever the quantities are finite, which holds when A or B is finite
--   - encoding: (1/2)‖ρ_ABE − ω_ABE‖₁ ≤ ε, ε ∈ [0,1], in ℝ → traceSize (ρ − ω) / 2 ≤ ENNReal.ofReal ε in ℝ≥0∞, with 0 ≤ ε ≤ 1 as real hypotheses; reason: the trace norm of a difference of states is a finite nonnegative real and ENNReal.ofReal ε = ε for ε ≥ 0; the same instances
-- source:
--   Wilde, Squashed entanglement and approximate private states, arXiv:1606.08028v3, eq. (21), p.6 (citing Shirokov, arXiv:1512.09047)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_SquashedKey_Information
import Definitions.Def_SquashedKey_KeyBoundFunction

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

namespace SquashedKey

/-- **Uniform continuity of conditional mutual information, (21)** [Shi17], Wilde, *Squashed
entanglement and approximate private states*, arXiv:1606.08028v3, §2.4, (21), p.6 (PDF p.6): "The
following uniform bound for continuity of conditional quantum mutual information holds as well
[Shi17]: `|I(A; B|E)_ρ − I(A; B|E)_ω| ≤ 2ε log₂ min{dim(H_A), dim(H_B)} + 2(1 + ε)h₂(ε/[1 + ε])`
for states `ρ_ABE, ω_ABE ∈ D(H_ABE)` such that `(1/2)‖ρ_ABE − ω_ABE‖₁ ≤ ε ∈ [0, 1]`."

Let `X`, `Y`, `Z` be arbitrary types, `ρ`, `ω` states on `(X × Y) × Z` and `ε ∈ [0, 1]` with
`½‖ρ − ω‖₁ ≤ ε`. Write `c(d) = 2ε log₂ d + 2(1 + ε) h₂(ε/(1 + ε))` (this is `f₁(ε, d)` of (46)).

1. If `X` is finite, then `I(X; Y|Z)_ρ ≤ I(X; Y|Z)_ω + c(|X|)` and
   `I(X; Y|Z)_ω ≤ I(X; Y|Z)_ρ + c(|X|)`.
2. If `Y` is finite, the same two inequalities hold with `c(|Y|)`.

**Formalization Note** `I` is the extended conditional mutual information in bits (`cmiBits`), in
`ℝ≥0∞`; the absolute value of a difference is written as two one-sided inequalities (no `∞ − ∞`).
The two clauses together give the `min{dim H_A, dim H_B}` of the display: when both systems are
finite both bounds hold, in particular the one with the smaller dimension; when only one is finite
the minimum is its dimension. The other system and the conditioning system `Z` are arbitrary
(infinite allowed). When neither system is finite the right-hand side of (21) is infinite and there
is nothing to state. -/
theorem eq_21_cmi_continuity {X Y Z : Type} (ρ ω : State ((X × Y) × Z)) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hclose : traceSize (ρ.coefficients - ω.coefficients) / 2 ≤ ENNReal.ofReal ε) :
    (Finite X →
        cmiBits ρ.coefficients ≤ cmiBits ω.coefficients + ENNReal.ofReal (f₁ ε (Nat.card X)) ∧
          cmiBits ω.coefficients ≤ cmiBits ρ.coefficients + ENNReal.ofReal (f₁ ε (Nat.card X))) ∧
      (Finite Y →
        cmiBits ρ.coefficients ≤ cmiBits ω.coefficients + ENNReal.ofReal (f₁ ε (Nat.card Y)) ∧
          cmiBits ω.coefficients ≤ cmiBits ρ.coefficients +
            ENNReal.ofReal (f₁ ε (Nat.card Y))) := by sorry

end SquashedKey
