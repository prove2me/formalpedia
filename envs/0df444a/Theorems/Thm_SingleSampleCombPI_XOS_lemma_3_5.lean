-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_lemma_3_5
-- name    : SingleSampleCombPI.XOS.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:09:17.16333+00:00
-- url     : https://prove2.me/theorems/ad4cd790-e1c1-459c-8962-55994ef90500
-- title:
--   Lemma 3.5 — replayed real allocations keep a (1−q) fraction of the sample run's free-disposal value
-- statement:
--   Fix any random-order free-disposal algorithm FDAlg and, for every buyer $i$, a pair of buyer types with supporting prices; the sample $s'_i$ and real $r'_i$ are assigned by an independent fair coin. In Algorithm 3 with role probability $q\in[0,1]$, let $x_i=\mathrm{PAlloc}_i(s^c,r_i)$ be the replayed real provisional allocation and $z_i=\mathrm{PAlloc}_i(s^c,s^c_i)$ the allocation of the sample run. Then
--   $$\mathbb E[\mathrm{FD}(x_1,\dots,x_n)]\ \ge\ (1-q)\,\mathbb E[\mathrm{FD}(z_1,\dots,z_n)],$$
--   where $\mathrm{FD}(x)$ uses the supporting prices of the real profile $r$ passed to Algorithm 1 and $\mathrm{FD}(z)$ those of the coordination sample $s^c$. The expectation covers the coins, the role coins, the processing order and FDAlg's randomness.
--
--   This is the replay comparison behind Theorem 3.6.
--
--   Differences from the source:
--   - encoding: a valuation v with its supporting-price map q_v (and, for computation, oracle access) → a record Buyer m with fields v, q (supporting-price oracle) and d (demand oracle) on vectors in ℝ^m, bundles as indicator vectors; reason: values off A^m are never used; the paper's per-valuation map q_v is the record's q
--   - encoding: an algorithm's internal randomness and expected nonnegative reward → an arbitrary probability space of seeds, with nonnegative lower integrals and finite external random choices averaged inside the seed integrals; independent item seeds use iterated expectations; reason: this includes discrete and atomless randomness; on measurable source payoffs these are ordinary expectations under the independent probability laws, without restricting valuation or allocation domains
--   - encoding: expectations and comparisons of nonnegative real quantities → expectations in ℝ≥0∞ of ENNReal.ofReal of the quantities; reason: all compared quantities are nonnegative under the hypotheses, so no instance changes and no integrability convention is needed
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, printed p. 16 / PDF p. 18, Lemma 3.5; proof in Appendix C, PDF pp. 40–41

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Online

namespace SingleSampleCombPI.XOS

/-- **Lemma 3.5** (Chawla–Dang, STOC 2027 submission #30, printed p. 16 / PDF p. 18; proof in
Appendix C).  For every random-order free-disposal algorithm `FDAlg`, every family of
single-sample Game-of-Googol pairs and every `q ∈ [0,1]`, in Algorithm 3 the replayed real
provisional allocations `x_i = PAlloc_i(sᶜ, r_i)` and the sample-run allocations
`z_i = PAlloc_i(sᶜ, sᶜ_i)` satisfy `E[FD(x_1, …, x_n)] ≥ (1 - q) E[FD(z_1, …, z_n)]`, where `FD(x)`
uses the supporting prices of the real profile `r` and `FD(z)` those of `sᶜ`. -/
theorem lemma_3_5 (A : Regime) {n m : ℕ} (F : FDAlg A n m) (V : Fin n → Fin 2 → Buyer m)
    (hV : ∀ i t, (V i t).Valid A) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (1 - q) *
        pexp F.seed (fun ω => avg (fun c : Fin n → Bool => bernExp q (fun H =>
          avg (fun π : Equiv.Perm (Fin n) =>
            ENNReal.ofReal (FD A (roleSc H (fun i => (gogPair (V i) (c i)).1))
              (replayZ F H π ω (fun i => (gogPair (V i) (c i)).1))))))) ≤
      pexp F.seed (fun ω => avg (fun c : Fin n → Bool => bernExp q (fun H =>
        avg (fun π : Equiv.Perm (Fin n) =>
          ENNReal.ofReal (FD A (roleR H (fun i => (gogPair (V i) (c i)).2))
            (replayX F H π ω (fun i => (gogPair (V i) (c i)).1)
              (fun i => (gogPair (V i) (c i)).2))))))) := by sorry

end SingleSampleCombPI.XOS
