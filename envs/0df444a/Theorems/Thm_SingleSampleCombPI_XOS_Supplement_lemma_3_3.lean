-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_lemma_3_3
-- name    : SingleSampleCombPI.XOS.Supplement.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:40:59.1164+00:00
-- url     : https://prove2.me/theorems/76832007-2a79-4e7b-b58b-e8d66bf6cc9c
-- title:
--   Lemma 3.3 — Buyer-local replay retains half the free-disposal reward of any random-order FDAlg
-- statement:
--   Fix any random-order free-disposal algorithm and two valid supporting-price buyer types per buyer, in either the indivisible or divisible regime. Independently swap each pair fairly into a sample and a real type. Algorithm 2 runs the algorithm on the sample in a shared uniform order and replays each real buyer from that buyer’s saved sample state. Its provisional allocation is buyer-local, and
--   $$\mathbb E[\mathrm{FD}(\mathrm{PAlloc}(s,r))]\ge\tfrac12\mathbb E[\mathrm{FD}(\mathrm{FDAlg}(r))].$$
--   Both expectations include the algorithm’s seed and the uniform auxiliary order. The real buyers may arrive adversarially. This comparison requires no competitive guarantee for the original free-disposal algorithm.
--
--   Differences from the source:
--   - encoding: valuations and one-sided supporting-price maps on the source allocation domains → published Buyer, Regime and cube interfaces with real-valued functions evaluated only on the allocation domain; reason: the stored demand field is unused in noncomputational continuous statements; no support, continuity or concavity condition is added to the source valuation class
--   - encoding: expectations over random seeds, uniform permutations and independent GoG assignments → published nonnegative lower expectations in ENNReal with explicit finite averages and arbitrary probability spaces of internal seeds; reason: for measurable source payoffs these are the ordinary expectations; no finite-support or atomless-input restriction is introduced
--   - encoding: PAlloc is buyer-local → replay F has the published PAlloc type, whose local function receives only the coordination sample, shared seed, buyer index and that buyer’s real type; reason: buyer-locality is structural in the type; the theorem states the remaining one-half reward comparison
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Lemma 3.3, printed p. 14 / PDF p. 16; proof printed 14–15 / PDF 16–17.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Online

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- Lemma 3.3, printed p. 14 / PDF p. 16. Buyer-locality is enforced by
`replay F : PAlloc A n m`: after fixing the sample and shared seed, `loc`
receives only the arriving buyer's type. The comparison is for any FD algorithm,
without a competitiveness premise, in either resource regime. -/
theorem lemma_3_3 (A : Regime) {n m : ℕ} (F : FDAlg A n m)
    (V : Fin n → Fin 2 → Buyer m) (hV : ∀ i t, (V i t).Valid A) :
    (1 / 2 : ℝ≥0∞) *
      pexp F.seed (fun ω => avg (fun c : Fin n → Bool =>
        avg (fun π : Equiv.Perm (Fin n) =>
          ENNReal.ofReal (FD A (fun i => (gogPair (V i) (c i)).2)
            (fdRun F ω π (fun i => (gogPair (V i) (c i)).2)))))) ≤
      pexp (replay F).seed (fun ω => avg (fun c : Fin n → Bool =>
        ENNReal.ofReal (FD A (fun i => (gogPair (V i) (c i)).2)
          (fun i => ((replay F).loc ω (fun j => (gogPair (V j) (c j)).1)
            i (gogPair (V i) (c i)).2).1)))) := by sorry

end SingleSampleCombPI.XOS.Supplement
