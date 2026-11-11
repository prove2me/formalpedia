-- Prove2me | Theorems.Thm_QMAvsQCMAH_theorem_7
-- name    : QMAvsQCMAH.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:20:45.208284+00:00
-- url     : https://prove2.me/theorems/b6d56b13-5a5b-498a-9602-b2e25ba38173
-- title:
--   Theorem 7 — switching with sparse answers
-- statement:
--   Fix integers $b,k,h\ge1$ and a DNF $f$ of width at most $k$ on a finite domain $\mathcal X$. There is a mapping $\mathrm{Switch}_{f,h}:(P,U)\mapsto T_{P,U}$ to deterministic classical algorithms that output one bit using fewer than $h$ queries to any oracle $r:P\to\{0,1\}$, such that the following holds. Suppose that $0<\rho^{1/b}\le1/(16bk)$ and that $P$ is random with $\Pr_P[u_1,\dots,u_t\in P]\le\rho^t$ ($1\le t\le bk+h$) for distinct $u_1,\dots,u_t\in\mathcal X$. Independently of $P$, sample $B\leftarrow\mathrm{Bernoulli}(2^{-b})^{\mathcal X}$ and put $U=B|_{\mathcal X\setminus P}$. Then, for the restricted function $g^{P,U}$,
--   $$\Pr_{P,B}\bigl[\forall r:P\to\{0,1\}:\ T^r_{P,U}=g^{P,U}(r)\bigr]\ge1-2(8bk\rho^{1/b})^h.$$
--
--   Differences from the source:
--   - generalization: a finite domain X ⊆ {0,1}* → any finite type X; reason: a finite subset of {0,1}* is such a type
--   - encoding: 0 < ρ^{1/b} → 0 < ρ with the real power ρ^{1/b}; reason: the b-th root is positive exactly for ρ > 0
--   - encoding: deterministic algorithms with fewer than h queries to r : P → {0,1} → decision trees of depth < h with all labels in P, run on O_r; reason: only the values on P are read
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Theorem 7, p.36 (PDF p.39), Equation (35)

import Definitions.Def_QMAvsQCMAH_DNF
import Definitions.Def_QMAvsQCMAH_DTree
import Definitions.Def_QMAvsQCMAH_restrictFn
import Definitions.Def_QMAvsQCMAH_prob

set_option autoImplicit false

namespace QMAvsQCMAH

/-- **Theorem 7 (Switching with sparse answers).** Fix integers `b, k, h ≥ 1` and a DNF `f` of
width at most `k` on a finite domain `X`. There is a mapping `Switch_{f,h} : (P, U) ↦ T_{P,U}` to
deterministic classical algorithms that output one bit using fewer than `h` queries to any
oracle `r : P → {0,1}`, such that: whenever `0 < ρ^{1/b} ≤ 1/(16bk)` and `P` is random with
`Pr_P[u_1, …, u_t ∈ P] ≤ ρ^t` (`1 ≤ t ≤ bk + h`) for distinct `u_1, …, u_t`, and, independently,
`B ← Bernoulli(2^{−b})^X`, `U = B|_{X∖P}`,
`Pr_{P,B}[∀r : P → {0,1} : T^r_{P,U} = g^{P,U}(r)] ≥ 1 − 2(8bkρ^{1/b})^h`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Theorem 7, p.36 (PDF p.39), Equation (35): "Fix integers b, k, h ≥ 1 and a DNF f of width
at most k on a finite domain X ⊆ {0, 1}∗. There is a mapping Switch_{f,h} : (P, U) ↦ T_{P,U} to
deterministic classical algorithms that output one bit using fewer than h queries to any oracle
r : P → {0, 1}. Suppose that 0 < ρ^{1/b} ≤ 1/(16bk) and that P is random with
Pr_P[u1, …, ut ∈ P] ≤ ρ^t (1 ≤ t ≤ bk + h) for distinct u1, …, ut ∈ X. Independently of P, sample
B ← Bernoulli(2^{−b})^X, U = B|_{X\P}. The mapping and algorithms may have unrestricted local
computation and description length. For the restricted function g^{P,U} (Definition 23),
Pr_{P,B}[∀r : P → {0, 1} : T^r_{P,U} = g^{P,U}(r)] ≥ 1 − 2(8bkρ^{1/b})^h."

**Formalization Note.** The mapping is chosen from `(f, h)` (and `b, k`) before `ρ` and the law
of `P` (paper pitfall 8). `T_{P,U}` is a decision tree with all queries in `P` and depth `< h`,
run on `O_r` (only `r` is read). `0 < ρ^{1/b}` is `0 < ρ` (the real `b`-th root). -/
theorem theorem_7 {X : Type} [Fintype X] [DecidableEq X] (b k h : ℕ) (hb : 1 ≤ b) (hk : 1 ≤ k) (hh : 1 ≤ h) (f : DNF X) (hf : DNF.width f ≤ k) : ∃ Switch : (P : Finset X) → ({u // u ∉ P} → Bool) → DTree X Bool, (∀ P U, (Switch P U).depth < h ∧ (Switch P U).LabelsIn ↑P) ∧ ∀ ρ : ℝ, 0 < ρ → ρ ^ ((1 : ℝ) / b) ≤ 1 / (16 * b * k) → ∀ μ : Finset X → ℝ, IsDist μ → (∀ S : Finset X, 1 ≤ S.card → S.card ≤ b * k + h → prob μ (fun P => S ⊆ P) ≤ ρ ^ S.card) → 1 - 2 * (8 * b * k * ρ ^ ((1 : ℝ) / b)) ^ h ≤ ∑ P : Finset X, ∑ B : X → Bool, μ P * bernW ((2 : ℝ)⁻¹ ^ b) B * (if ∀ r : {u // u ∈ P} → Bool, (Switch P (offP B P)).eval (oFrom P (offP B P) r) = restrictFn (fun O => DNF.eval f O) P (offP B P) r then 1 else 0) := by sorry

end QMAvsQCMAH
