-- Prove2me | Theorems.Thm_RandOrderCSP_lemma_10_3
-- name    : RandOrderCSP.lemma_10_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:09:57.705194+00:00
-- url     : https://prove2.me/theorems/008cd6ce-834c-4b37-9e5d-dca634717511
-- title:
--   Lemma 10.3 — preservation of the CSP optimum
-- statement:
--   Fix $k\ge2$ and a finite alphabet $\Sigma$. For every $\eta>0$ there is $D\in\mathbb N^+$ such that for every $k$-CSP $\Phi$ with alphabet $\Sigma$ and at least one edge, for $\Phi'\sim\mathrm{Regular}_D(\Phi)$,
--
--   $$\mathrm{opt}_\Phi\le\mathrm{opt}_{\Phi'}\ \text{ deterministically},\qquad\mathbb E\,\mathrm{opt}_{\Phi'}\le\mathrm{opt}_\Phi+\eta.$$
--
--   Regularization thus reduces the degree to a constant at a small cost in the optimum.
--
--   Differences from the source:
--   - encoding: there exists D ∈ ℕ → 1 ≤ D; reason: Regular_D is defined for D ∈ ℕ⁺ (p.49)
--   - encoding: every k-CSP Φ → the edge set is nonempty and k ≥ 2; reason: the standing assumptions of §10, p.48
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Lemma 10.3, p.50

import Mathlib
import Definitions.Def_RandOrderCSP_regularize

namespace RandOrderCSP

/-- **Lemma 10.3 (preservation of the CSP optimum).** Singer, Tulsiani, Velusamy, *A dichotomy theorem for
approximating CSPs in random-order streams*, STOC 2027 submission (manuscript sha256 3aca9d2f…),
Lemma 10.3, p.50.

**Formalization Note.** "Deterministically" is: for every cloud permutation family. `k ≥ 2` and at least
one edge are §10's standing assumptions (p.48), and `Regular_D` is defined for `D ≥ 1` (p.49). `D` depends
on `k`, `Σ`, `η` only (p.51). -/
theorem lemma_10_3 {k : ℕ} (hk : 2 ≤ k) (Sig : Type) [Fintype Sig] [Nonempty Sig] (η : ℝ) (hη : 0 < η) :
    ∃ D : ℕ, 1 ≤ D ∧
      ∀ (V E : Type) [Fintype V] [Fintype E] [Nonempty E] (Φ : CSP k Sig V E),
        (∀ P : CloudFamily Φ.H D, Φ.opt ≤ (CSP.regularize Φ P).opt) ∧
        regularAvg Φ.H D (fun P => (CSP.regularize Φ P).opt) ≤ Φ.opt + η := by sorry

end RandOrderCSP
