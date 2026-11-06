-- Prove2me | Theorems.Thm_TIESharp_lemma_5_1
-- name    : TIESharp.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:09.70327+00:00
-- url     : https://prove2.me/theorems/b5f38678-d2cf-4b69-a5c4-702e75f4c84d
-- title:
--   Lemma 5.1 — payments for column-local probabilities
-- statement:
--   Fix a job count $m$. Suppose $q_{ij}(t)\ge0$, $\sum_iq_{ij}(t)=1$, and $q_{ij}$ depends only on column $t_{\cdot j}$. Fixing the other entries in that column, suppose $q(s)=q_{ij}(s,t_{-ij})$ is nonincreasing on $[0,\infty)$ and $\int_0^\infty q(u)\,du<\infty$. Then any assignment distribution realizing these probabilities is truthful in expectation with per-job expected payment
--   $$\pi(s)=s\,q(s)+\int_s^\infty q(u)\,du,\tag{5.1}$$
--   each machine's expected payment being the sum of its per-job payments. These payments and the expected utilities at every finite true type and finite deviation are finite.
--
--   The joint law may correlate the jobs arbitrarily; only the marginals and the payments enter truthfulness in expectation.
--
--   Differences from the source:
--   - generalization: §§3–5 standing assumption n ≥ 2 (p.4) → every n; reason: the statement and proof are per machine and per job; n ≥ 2 is a specialization
--   - encoding: q_ij depends only on column t_{·j} → q_ij(t) = Q j i (t_{·j}) for a rule Q j of the column, hypotheses on nonnegative columns; reason: exactly a column-local rule; it may differ between jobs, as the page allows
--   - encoding: finite payments and utilities; ∫_0^∞ q < ∞ → real-valued payments; IntegrableOn of u ↦ q(u) on (0, ∞); reason: for a nonnegative q, a finite integral is integrability
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 5.1, p.22, (5.1)

import Mathlib
import Definitions.Def_TIESharp_Nonneg

set_option autoImplicit false

namespace TIESharp

/-- **Lemma 5.1 (Payments for column-local probabilities)** (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, Lemma 5.1, p.22). At a job count `m`,
suppose `q_ij(t) ≥ 0`, `Σ_i q_ij(t) = 1`, and `q_ij` depends only on column `t_{·j}`. Fixing the
other entries in that column, suppose `q(s) = q_ij(s, t_{-ij})` is nonincreasing on `[0, ∞)` and
`∫_0^∞ q(u) du < ∞`. Then any assignment distribution realizing these probabilities is truthful in
expectation with per-job expected payment `π(s) = s q(s) + ∫_s^∞ q(u) du` (5.1), each machine's
expected payment being the sum of its per-job payments: for every machine `i`, nonnegative
opponents' bids, true row `t_i` and deviation `b_i`,
`p_i(t_i, b_{-i}) − t_i · q_i(t_i, b_{-i}) ≥ p_i(b_i, b_{-i}) − t_i · q_i(b_i, b_{-i})`.

**Formalization Note.** Job `j`'s rule is `Q j : Fin n → (Fin n → ℝ) → ℝ`, a function of the
column only (it may differ between jobs). Its hypotheses are imposed on nonnegative columns. The
assignment law `y b` is any probability vector over `Fin m → Fin n` with marginals `Q j i (b_{·j})`;
expected costs use these marginals. Payments are real, hence finite; integrability of
`u ↦ q(u)` on `(0, ∞)` is the paper's `∫_0^∞ q(u) du < ∞` for a nonnegative `q`. -/
theorem lemma_5_1 (n m : ℕ) (Q : Fin m → Fin n → (Fin n → ℝ) → ℝ)
    (hQnn : ∀ j i (c : Fin n → ℝ), (∀ a, 0 ≤ c a) → 0 ≤ Q j i c)
    (hQsum : ∀ j (c : Fin n → ℝ), (∀ a, 0 ≤ c a) → ∑ i, Q j i c = 1)
    (hQmono : ∀ j i (c : Fin n → ℝ), (∀ a, 0 ≤ c a) →
      AntitoneOn (fun s => Q j i (Function.update c i s)) (Set.Ici 0))
    (hQint : ∀ j i (c : Fin n → ℝ), (∀ a, 0 ≤ c a) →
      MeasureTheory.IntegrableOn (fun u => Q j i (Function.update c i u)) (Set.Ioi 0))
    (y : (Fin n → Fin m → ℝ) → (Fin m → Fin n) → ℝ)
    (hy : ∀ b : Fin n → Fin m → ℝ, Nonneg b →
      (∀ A, 0 ≤ y b A) ∧ ∑ A, y b A = 1 ∧
      ∀ i j, ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i), y b A
        = Q j i (fun a => b a j)) :
    ∀ (b : Fin n → Fin m → ℝ) (i : Fin n) (ti bi : Fin m → ℝ),
      Nonneg b → (∀ j, 0 ≤ ti j) → (∀ j, 0 ≤ bi j) →
        (∑ j, ((Function.update b i bi) i j * Q j i (fun a => Function.update b i bi a j)
            + ∫ u in Set.Ioi ((Function.update b i bi) i j),
                Q j i (Function.update (fun a => Function.update b i bi a j) i u)))
          - ∑ j, ti j * ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i),
              y (Function.update b i bi) A
        ≤ (∑ j, ((Function.update b i ti) i j * Q j i (fun a => Function.update b i ti a j)
            + ∫ u in Set.Ioi ((Function.update b i ti) i j),
                Q j i (Function.update (fun a => Function.update b i ti a j) i u)))
          - ∑ j, ti j * ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i),
              y (Function.update b i ti) A := by sorry

end TIESharp
