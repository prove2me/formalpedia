-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_F_3
-- name    : QuantumKtSoI.Supplement.theorem_F_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:58:16.496493+00:00
-- url     : https://prove2.me/theorems/7057a3b7-9b71-496d-9b13-512b2f3fb86b
-- title:
--   Theorem F.3, p.231 — robustness of the time charge: the main results hold for $\mathrm{qKt}^{(c)}$
-- statement:
--   Let $c>0$ be real, and let $\mathrm{qKt}^{(c)}_\varrho(y|x)=\min\{|e|+c\lceil\log t\rceil : P_e(x;t,y)\ge\varrho\}$ with $\mathrm{qKt}^{(c)}=\mathrm{qKt}^{(c)}_{2/3}$. The following results hold with $\mathrm{qKt}^{(c)}$ in place of $\mathrm{qKt}$ in their statements and in the definitions they use. The error scales, the clock family and the polynomial $p(n)=8000n^2$ of Theorem 5.16 are unchanged; every constant and every machine asserted to exist may depend on $c$.
--
--   1. (a) Theorem 4.13 and Corollaries 4.14 and 4.15, with the lower threshold function written $s_0$.
--   2. (b), for rational $c$: Theorem 5.10 and Corollary 5.13.
--   3. (c), for rational $c$: Theorem 5.16.
--   4. (d), for rational $c$: Theorems 5.22 and 5.25 and Corollary 5.24.
--   5. (e) Theorems A.1 and 8.3 and Propositions A.2 and 8.4.
--   6. (f), for rational $c$: Theorem 6.14 and Corollary 6.15, with the absolute constant $c_{\mathrm{sym}}$ replaced by a constant that depends only on $c$.
--   7. For rational $c<2$: Theorem 7.3 holds for $\mathrm{qKt}^{(c)}$ with the gap $\lfloor(1-c/2-\eta)\lambda\rfloor$ for rational $\eta\in(0,1-c/2)$ and the time bound $2^{\varepsilon\nu}$, $\varepsilon=\eta/(40\max(c,1))$ (Proposition G.1).
--
--   So the coefficient one of $\lceil\log t\rceil$ in the definition of $\mathrm{qKt}$ is not essential to the main results.
--
--   **Formalization Note** Each restated result is a measure-parameterized proposition of the definition modules, instantiated at $\mathrm{qKt}^{(c)}$ (and at $\mathrm{qKt}^{(c)}_\varrho$ for Corollary 4.15); at $\mathrm{qKt}$ it is the paper's statement. "$c$ rational" is $c=q$ for a rational $q$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
--   - reading: the classical polynomial-time samplers of Theorems A.1, 8.3 and Propositions A.2, 8.4 → probabilistic Turing machines with an all-branch polynomial deadline (PolySampler, GSampler); reason: the reading of the published goal of the base mission
--   - reading: Promise-BQTIME[n^{polylog(n)}] in Corollary 4.15 → for every integer a₀ ≥ 1 and constant C, no machine decides the problem in time C·n^{(log(n+2))^{a₀}}; reason: p.22: the family is {n^{(log(n+2))^a}} and deciding within O(T) is deciding within cT for a constant c
--   - reading: Proposition G.1 for every g computable in time polynomial in the value of its argument; "an encoding", "decidable in time polynomial in N" and the oracle-free conventions of the restated results → the same pinned readings as in the items for Theorems 7.3, 8.3 and A.1 (PolyInValue, injective Enc, decision on input b(N)); reason: one reading per notion across the mission
--   - encoding: E[T_x] and "halts with output 1 with probability" in Corollary 4.14 → E[T_x] = Σ_t (1 − Pr[T_x ≤ t]) in [0,∞] with Pr[T_x ≤ t] the weight of the halted branches; the halting probability is sup_t P_A(x; t, 1); reason: the paper's definitions on p.50 (a nondecreasing bounded sequence converges to its supremum)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem F.3, p.231; Definition 4.2, p.41; conventions for qKt^{(c)}, p.229; Proposition G.1, p.245

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_qKtChargeRho
import Definitions.Def_QuantumKtSoI_Supplement_Thm413For
import Definitions.Def_QuantumKtSoI_Supplement_SoIFailures
import Definitions.Def_QuantumKtSoI_Supplement_Thm525For
import Definitions.Def_QuantumKtSoI_Supplement_Thm83For
import Definitions.Def_QuantumKtSoI_Supplement_Thm614For

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem F.3** (Robustness of the time charge; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.231). Let `c > 0` be real; parts (b),
(c), (d) and (f) assume moreover that `c` is rational. The following results hold with `qKt^{(c)}`
in place of `qKt` in their statements and in the definitions they use; the error scales, the clock
family and the polynomial `p(n) = 8000n²` of Theorem 5.16 are unchanged, and every constant and
machine asserted to exist may depend on `c`.
(a) Theorem 4.13 and Corollaries 4.14 and 4.15 (lower threshold written `s₀`).
(b) Theorem 5.10 and Corollary 5.13.
(c) Theorem 5.16.
(d) Theorems 5.22 and 5.25 and Corollary 5.24.
(e) Theorems A.1 and 8.3 and Propositions A.2 and 8.4.
(f) Theorem 6.14 and Corollary 6.15, with `c_sym` replaced by a constant that depends only on `c`.
Theorem 7.3 holds for `qKt^{(c)}` whenever `c < 2` is rational, with the gap `⌊(1 − c/2 − η)λ⌋` for
rational `η ∈ (0, 1 − c/2)` and the time bound `2^{εν}`, `ε = η/(40 max(c,1))` (Proposition G.1).

**Formalization Note** `qKt^{(c)}` is the published `qKtCharge G c` (Definition 4.2, threshold
`2/3`), and `qKt^{(c)}_ϱ` is `qKtChargeRho G c ϱ` (used by Corollary 4.15 through Definition 4.11).
Each restated result is the measure-parameterized proposition of the definition modules (`…For`),
which at `µ = qKt` is the paper's statement. "`c` rational" is `c = q` for a rational `q`. The
constants of each restated result are quantified inside it, after `c` (and after the admissible
glue routine set `G`, p.24, fixed first as in the base mission). -/
theorem theorem_F_3 (G : GlueRoutines) (hG : G.Admissible) (c : ℝ) (hc : 0 < c) :
    (Thm413For (fun x => qKtCharge G c x []) ∧ Cor414For (fun x => qKtCharge G c x []) ∧
      Cor415For (fun ϱ w => qKtChargeRho G c ϱ w [])) ∧
    (ThmA1For (qKtCharge G c) ∧ Thm83For (qKtCharge G c) ∧ PropA2For (qKtCharge G c) ∧
      Prop84For (qKtCharge G c)) ∧
    ((∃ q : ℚ, c = (q : ℝ)) →
      (Thm510For (qKtCharge G c) ∧ Cor513For (qKtCharge G c)) ∧
      Thm516For (qKtCharge G c) ∧
      (Thm522For (qKtCharge G c) ∧ Thm525For (qKtCharge G c) ∧ Cor524For (qKtCharge G c)) ∧
      (Thm614For (qKtCharge G c) ∧ Cor615For (qKtCharge G c))) ∧
    ∀ q : ℚ, c = (q : ℝ) → c < 2 → PropG1For q (fun x => qKtCharge G c x []) := by sorry

end QuantumKtSoI.Supplement
