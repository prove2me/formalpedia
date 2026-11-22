-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_F_4
-- name    : QuantumKtSoI.Supplement.theorem_F_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:59:22.201706+00:00
-- url     : https://prove2.me/theorems/3327ca20-8c9e-4afe-b1c6-6bb0ade9c993
-- title:
--   Theorem F.4, p.235 — a positive linear gap for every rational charge $c$
-- statement:
--   For every rational $c>0$ there are rational constants $\gamma_c,\varepsilon_c>0$ such that the following holds. For every function $g:\mathbb N\to\mathbb N$ computable in time polynomial in the value of its argument with $g(\lambda)\le\gamma_c\lambda$ for all large $\lambda$, no machine decides a language consistent with the gap $g$ for $\mathrm{qKt}^{(c)}$ infinitely often in time $2^{\varepsilon_c\nu}$. In particular, the conclusion holds for exact threshold decision, that is, for the gap $g=0$, and for every polynomial-time computable gap $g(\lambda)=o(\lambda)$.
--
--   Here a language is consistent with the gap $g$ for $\mathrm{qKt}^{(c)}$ if it contains the query $q(x,s)$ whenever $\mathrm{qKt}^{(c)}(x)\le s$ and excludes it whenever $\mathrm{qKt}^{(c)}(x)>s+g(|x|)$.
--
--   So an exponential lower bound for threshold decision holds at some linear gap for every charge, not only for $c<2$.
--
--   **Formalization Note** $\mathrm{qKt}^{(c)}$ is the published `qKtCharge`.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
--   - reading: g computable in time polynomial in the value of its argument (no input format named) → a deterministic coded machine on input b(λ) halts within c(λ+2)^k steps with output b(g(λ)); reason: with a bound polynomial in the value λ, unary and binary inputs give the same class
--   - reading: every polynomial-time computable gap g(λ) = o(λ) → g computable in time polynomial in the value of its argument with: for every δ > 0, eventually g(λ) ≤ δλ; reason: the same computability notion as in the main clause; the usual meaning of little-o
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem F.4, p.235; consistency for qKt^{(c)}, p.229

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_query
import Definitions.Def_QuantumKtSoI_Supplement_PolyInValue

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem F.4** (A positive linear gap for every charge; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.235). For every rational `c > 0`
there are rational constants `γ_c, ε_c > 0` such that, for every `g : ℕ → ℕ` computable in time
polynomial in the value of its argument with `g(λ) ≤ γ_c λ` for all large `λ`, no machine decides a
language consistent with the gap `g` for `qKt^{(c)}` infinitely often in time `2^{ε_c ν}`. In
particular, the conclusion holds for exact threshold decision, that is, for the gap `g = 0`, and for
every polynomial-time computable gap `g(λ) = o(λ)`.

**Formalization Note** `qKt^{(c)}` is the published `qKtCharge G c` (Definition 4.2, threshold
`2/3`); consistency with a gap for `qKt^{(c)}` (p.229) and the queries are those of §6.6 with
`µ(x) = qKt^{(c)}(x)`. "Polynomial-time computable" in the last clause is read as in the main
clause (`PolyInValue`), and `g(λ) = o(λ)` as: for every `δ > 0`, eventually `g(λ) ≤ δλ`. `G` is any
admissible glue routine set (p.24). -/
theorem theorem_F_4 (G : GlueRoutines) (hG : G.Admissible) :
    ∀ c : ℚ, 0 < c → ∃ γc εc : ℚ, 0 < γc ∧ 0 < εc ∧
      (∀ g : ℕ → ℕ, PolyInValue g →
        (∃ l₀ : ℕ, ∀ lam ≥ l₀, (g lam : ℝ) ≤ (γc : ℝ) * lam) →
        ∀ L : Set (List Bool), ConsistentGap (fun x => qKtCharge G c x []) g L →
          ¬∃ A : CodedMachine, A.Valid ∧ DecidesIO A L εc) ∧
      (∀ L : Set (List Bool), ConsistentGap (fun x => qKtCharge G c x []) (fun _ => 0) L →
        ¬∃ A : CodedMachine, A.Valid ∧ DecidesIO A L εc) ∧
      ∀ g : ℕ → ℕ, PolyInValue g →
        (∀ δ : ℝ, 0 < δ → ∃ l₀ : ℕ, ∀ lam ≥ l₀, (g lam : ℝ) ≤ δ * lam) →
        ∀ L : Set (List Bool), ConsistentGap (fun x => qKtCharge G c x []) g L →
          ¬∃ A : CodedMachine, A.Valid ∧ DecidesIO A L εc := by sorry

end QuantumKtSoI.Supplement
