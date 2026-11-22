-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_6_14
-- name    : QuantumKtSoI.Supplement.theorem_6_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:43:41.51671+00:00
-- url     : https://prove2.me/theorems/4be9f1bb-5964-40b9-ac6e-52bf33be0e07
-- title:
--   Theorem 6.14, p.85 — estimating $\mathrm{qKt}$ within $\psi$ in time $T$ gives symmetry of information with error $c_{\mathrm{sym}}(\lceil\log T(4L)\rceil+\psi(4L))+C\lceil\log(L+2)\rceil^3$
-- statement:
--   There is an absolute positive integer $c_{\mathrm{sym}}$ such that the following holds. Let $T,\psi:\mathbb N\to\mathbb N$ be nondecreasing with $T(n)\ge\max(n,1)$ and $\psi(n)\ge1$, and suppose that some machine estimates $\mathrm{qKt}$ within $\psi$ in time $T$ (Definition 6.12). Then there is a positive integer $C$, depending on the machine, $T$ and $\psi$, such that for all strings $x,y$, with $L=|x|+|y|$,
--   $$\mathrm{qKt}(y|x)\le\mathrm{qKt}(\langle x,y\rangle)-\mathrm{qKt}(x)+c_{\mathrm{sym}}\big(\lceil\log T(4L)\rceil+\psi(4L)\big)+C\lceil\log(L+2)\rceil^3 .$$
--
--   So efficient estimation of the measure would give symmetry of information with a correspondingly small error.
--
--   **Formalization Note** The inequality is stated in $\mathbb Z$ as a bound on the published defect $\Delta(x,y)$. $c_{\mathrm{sym}}$ is chosen after the glue routine set and before $T$, $\psi$ and the machine.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 6.14, p.85; Definition 6.12, p.83; Definition 5.3, p.52

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_Estimates

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem 6.14** (Estimation yields symmetry of information; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.85). Let `T, ψ : ℕ → ℕ`
be nondecreasing with `T(n) ≥ max(n, 1)` and `ψ(n) ≥ 1`, and suppose that some machine estimates
`qKt` within `ψ` in time `T`. Then `qKt` satisfies symmetry of information with error
`θ(L) = c_sym(⌈log T(4L)⌉ + ψ(4L)) + C⌈log(L+2)⌉³`, where `c_sym` is an absolute positive integer,
independent of `T`, `ψ` and the machine, and `C` is a positive integer that depends on the machine,
`T` and `ψ`.

**Formalization Note** `G` is any admissible glue routine set (p.24), fixed before `c_sym` (the
paper's model, glue routines included, is fixed once and for all). Symmetry of information with
error `θ` (Definition 5.3, p.52) is `Δ(x, y) ≤ θ(|x| + |y|)` for all `x, y`, written in `ℤ` with the
published `defect`. "Estimates within `ψ` in time `T`" is Definition 6.12 (`Estimates`, all-branch
halting). `⌈log m⌉` is `Nat.clog 2 m`. -/
theorem theorem_6_14 (G : GlueRoutines) (hG : G.Admissible) :
    ∃ csym : ℕ, 0 < csym ∧ ∀ T ψ : ℕ → ℕ, Monotone T → Monotone ψ → (∀ n, max n 1 ≤ T n) →
      (∀ n, 1 ≤ ψ n) → ∀ A : CodedMachine, A.Valid → Estimates (fun v => (qKt G v [] : ℝ)) A T ψ →
        ∃ C : ℕ, 0 < C ∧ ∀ x y : List Bool,
          defect G x y ≤
            ((csym * (Nat.clog 2 (T (4 * (x.length + y.length))) + ψ (4 * (x.length + y.length))) +
              C * Nat.clog 2 (x.length + y.length + 2) ^ 3 : ℕ) : ℤ) := by sorry

end QuantumKtSoI.Supplement
