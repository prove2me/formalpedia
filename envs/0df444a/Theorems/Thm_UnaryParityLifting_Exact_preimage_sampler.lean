-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_preimage_sampler
-- name    : UnaryParityLifting.Exact.preimage_sampler
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:29.968384+00:00
-- url     : https://prove2.me/theorems/b2cc34ed-1ea7-458c-aac3-4a81f61a84d7
-- title:
--   Lemma 3.6 — Sampling by partial assignments
-- statement:
--   Let $g:\{0,1\}^m\to\{0,1\}$ be surjective and 1-stifling, and set $\delta_g=2/(m\max_b|g^{-1}(b)|)$. There is one probability law on paired partial assignments $(\sigma_0,\sigma_1)$, chosen independently of the desired output bit. Every pair of positive probability has the same stars in its two components. For both $b=0,1$, selecting $\sigma_b$ and filling its stars with independent uniform bits gives a uniform element of $g^{-1}(b)$. Every coordinate satisfies
--   $$\Pr[\sigma_0(j)=*]=\Pr[\sigma_1(j)=*]\ge\delta_g.$$
--
--   The completion laws are equal at every atom, including zero probability outside the required fiber. The statement supplies both marginals jointly, rather than unrelated samplers depending on the requested output. This provides the paired sampling interface needed by the affine decomposition.
--
--   Differences from the source:
--   - encoding: coordinates indexed by [N] and [m], bits in {0,1} → Fin N and Fin m, Bool bits with false = 0 and true = 1; reason: zero-based labels and the explicit bit maps preserve every assignment
--   - encoding: surjective gadget convention of Definition 2.5, retained throughout Sections 3–4 → an explicit Function.Surjective g hypothesis; reason: excludes empty gadget fibers and the zero-bit vacuity of the reused stifling predicate without excluding any source gadget
--   - encoding: a random pair independent of b → one finite PairLaw, with both output completion laws quantified after that law; reason: the law cannot depend on b; independent fair filling is the explicit conditional atom probability
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), citation_basis: published; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/567.pdf; pp.9–10, Lemma 3.6, equations (3.3)–(3.4)

import Mathlib
import Definitions.Def_UnaryParityLifting_Exact_partialAssignments

namespace UnaryParityLifting.Exact

/-- Alekseev, STOC 2027 submission #567 (October 2026), pp.9–10, Lemma 3.6.
One law is chosen before the output bit; its two marginals have common stars. -/
theorem preimage_sampler (m : ℕ) (g : (Fin m → Bool) → Bool)
    (hg : Function.Surjective g) (hstifling : LiftSAParity.IsOneStifling g) :
    ∃ μ : PairLaw m,
      (∀ σ, μ.probability σ ≠ 0 → ∀ j, σ.1 j = none ↔ σ.2 j = none) ∧
      (∀ b x, completionLaw μ b x = fiberProbability g b x) ∧
      (∀ j, starProbability μ false j = starProbability μ true j ∧
        gadgetDelta g ≤ starProbability μ false j) := by sorry

end UnaryParityLifting.Exact
