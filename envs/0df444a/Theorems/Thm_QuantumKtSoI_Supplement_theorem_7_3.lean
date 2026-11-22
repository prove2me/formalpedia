-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_7_3
-- name    : QuantumKtSoI.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:45:11.064804+00:00
-- url     : https://prove2.me/theorems/9c4f72a6-d586-4487-b9d3-3685f810abfe
-- title:
--   Theorem 7.3, p.100 — no machine decides a language consistent with a gap $g\le(1/2-\eta)\lambda$ infinitely often in time $2^{\eta\nu/40}$
-- statement:
--   Let $\eta$ be a rational number with $0<\eta<1/2$ and put $\varepsilon=\eta/40$. With the encoded queries $q(x,s)=\langle x,\mathrm{bin}_{\mathrm{wd}(\lambda)}(s)\rangle$ of length $\nu(\lambda)$:
--
--   1. for every $g:\mathbb N\to\mathbb N$ that is computable in time polynomial in the value of its argument and satisfies $g(\lambda)\le(1/2-\eta)\lambda$ for all large $\lambda$, no machine decides a language consistent with the gap $g$ infinitely often in time $2^{\varepsilon\nu}$;
--   2. the conclusion holds for $g(\lambda)=\lfloor(1/2-\eta)\lambda\rfloor$;
--   3. it also holds for $g(\lambda)=\lceil c\log(\lambda+2)\rceil$ with any constant $c\ge0$;
--   4. in particular, no machine decides $L_{\mathrm{thr}}=\{q(x,s):\mathrm{qKt}(x)\le s\}$ infinitely often in time $2^{\varepsilon\nu}$.
--
--   A language is consistent with the gap $g$ if it contains $q(x,s)$ whenever $\mathrm{qKt}(x)\le s$ and excludes it whenever $\mathrm{qKt}(x)>s+g(|x|)$.
--
--   This is the exponential lower bound for deciding threshold languages of quantum Kt complexity.
--
--   **Formalization Note** Clauses 2 and 3 are stated without a computability hypothesis on the gap, as in the paper.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
--   - reading: g computable in time polynomial in the value of its argument (no input format named) → a deterministic coded machine on input b(λ) halts within c(λ+2)^k steps with output b(g(λ)); reason: with a bound polynomial in the value λ, unary and binary inputs give the same class
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 7.3, p.100; queries and consistency, p.96; L_thr and deciding infinitely often, p.98

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_query
import Definitions.Def_QuantumKtSoI_Supplement_PolyInValue

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem 7.3** (Consistent threshold-language decision takes exponential time; restatement of
Theorem 1.4; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.100). Let `η` be rational with `0 < η < 1/2` and put `ε = η/40`. For every
`g : ℕ → ℕ` computable in time polynomial in the value of its argument with `g(λ) ≤ (1/2 − η)λ` for
all large `λ`, no machine decides a language consistent with the gap `g` infinitely often in time
`2^{εν}`. The conclusion holds for `g(λ) = ⌊(1/2 − η)λ⌋` and also for `g(λ) = ⌈c log(λ+2)⌉` with any
constant `c ≥ 0`; in particular no machine decides `L_thr` infinitely often in time `2^{εν}`.

**Formalization Note** The queries `q(x, s)`, `wd`, `ν`, consistency with a gap and `L_thr` are
those of §6.6 and p.98 (module `query`) for `µ(x) = qKt(x)`; "decides infinitely often in time
`2^{εν}`" is `DecidesIO`. The two special gaps are stated without a computability hypothesis, as
in the paper (`c` need not be computable). `G` is any admissible glue routine set (p.24). -/
theorem theorem_7_3 (G : GlueRoutines) (hG : G.Admissible) (η : ℚ) (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    (∀ g : ℕ → ℕ, PolyInValue g →
      (∃ l₀ : ℕ, ∀ lam ≥ l₀, (g lam : ℝ) ≤ (1 / 2 - (η : ℝ)) * lam) →
      ∀ L : Set (List Bool), ConsistentGap (fun x => (qKt G x [] : ℝ)) g L →
        ¬∃ A : CodedMachine, A.Valid ∧ DecidesIO A L ((η : ℝ) / 40)) ∧
    (∀ L : Set (List Bool),
      ConsistentGap (fun x => (qKt G x [] : ℝ)) (fun lam => ⌊(1 / 2 - (η : ℝ)) * lam⌋₊) L →
        ¬∃ A : CodedMachine, A.Valid ∧ DecidesIO A L ((η : ℝ) / 40)) ∧
    (∀ c : ℝ, 0 ≤ c → ∀ L : Set (List Bool),
      ConsistentGap (fun x => (qKt G x [] : ℝ))
          (fun lam => ⌈c * Real.logb 2 ((lam : ℝ) + 2)⌉₊) L →
        ¬∃ A : CodedMachine, A.Valid ∧ DecidesIO A L ((η : ℝ) / 40)) ∧
    ¬∃ A : CodedMachine, A.Valid ∧ DecidesIO A (Lthr fun x => (qKt G x [] : ℝ)) ((η : ℝ) / 40) := by sorry

end QuantumKtSoI.Supplement
