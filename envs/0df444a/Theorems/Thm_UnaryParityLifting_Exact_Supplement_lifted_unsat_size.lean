-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_Supplement_lifted_unsat_size
-- name    : UnaryParityLifting.Exact.Supplement.lifted_unsat_size
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:48:55.044568+00:00
-- url     : https://prove2.me/theorems/f43afaa3-a483-48d9-849a-5ecdfc218996
-- title:
--   Lemma 6.1 — Unsatisfiability and encoding size
-- statement:
--   Fix a surjective 1-stifling gadget g on m≥1 bits. With F_n=SoD_(n²), the exact all-falsifying-assignment lift F_n∘g is unsatisfiable for every n≥1. There are natural K and n₀≥2, depending only on g, such that
--
--   $$L_n=|F_n\circ g|\le n^K\qquad(n\ge n_0).$$
--
--   Here length is the ordinary binary listing including variable indices. This supplies both the soundness and actual encoding-length input to the incomparability theorem. The eventual interpretation of the polynomial length bound is the asymptotic range used throughout §6.
--
--   Differences from the source:
--   - encoding: binary encoding length with an implicit asymptotic range → fixed explicit binary listing and an existential threshold n₀≥2; unsatisfiability for every positive n; reason: finite listing conventions change only fixed overhead and the brief pins the polynomial bound to its asymptotic range
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), printed/PDF p.19, Lemma 6.1

import Definitions.Def_UnaryParityLifting_Exact_Supplement_sinkDAG
import Definitions.Def_UnaryParityLifting_Exact_averaging

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- Lemma 6.1; unsatisfiability for every positive parameter, size eventually. -/
theorem lifted_unsat_size {m : ℕ} (g : (Fin m → Bool) → Bool)
    (hm : 1 ≤ m) (hg : Function.Surjective g) (hs : LiftSAParity.IsOneStifling g) :
    (∀ n : ℕ, 1 ≤ n → ¬ LiftSAParity.Satisfiable (liftedSink g n)) ∧
    ∃ K n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → liftedLength g n ≤ n ^ K := by sorry

end UnaryParityLifting.Exact.Supplement
