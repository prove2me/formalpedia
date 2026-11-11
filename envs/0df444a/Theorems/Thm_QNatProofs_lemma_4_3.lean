-- Prove2me | Theorems.Thm_QNatProofs_lemma_4_3
-- name    : QNatProofs.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:53.651806+00:00
-- url     : https://prove2.me/theorems/c3d9d6ee-8f0c-401f-842c-2152fff7b039
-- title:
--   Lemma 4.3 — finite sampler approximation
-- statement:
--   There is an absolute constant $c$ such that for every approximation error $\xi\in(0,1)$ and failure probability $\eta\in(0,1)$ there are sampler parameters $\mu\ge1$, $K_{\max}$ and $q$ with
--   $$
--   \mu,\ K_{\max},\ q\ \le\ c\,\big(\log(2/\xi)+\log(2/\eta)\big)\tag{38}
--   $$
--   such that, for every admissible choice of thresholds (36), the output $V_{\mathrm{fin}}$ of the finite Poisson sampler can be coupled with $G\sim\mathcal N_{\mathbb C}(0,1)$ so that
--   $$
--   \Pr\big[|\sqrt\mu\,V_{\mathrm{fin}}-G|>\xi\big]\le\eta;\tag{39}
--   $$
--   that is, the finite Poisson sampler is a $(\sqrt\mu,\xi,\eta)$-complex Gaussian sampler.
--
--   This is the statistical guarantee of the sampler used in Lemma 4.1.
--
--   Differences from the source:
--   - encoding: µ, K_max, q = O(log(2/ξ) + log(2/η)) → one absolute constant c and the three bounds ≤ c(log(2/ξ) + log(2/η)) (natural log); reason: the meaning of O(·), uniform in ξ, η
--   - generalization: the finite Poisson sampler, whose thresholds are chosen to satisfy (36) → the coupling for every admissible threshold choice (36), and µ a natural number ≥ 1; reason: a stronger conclusion; the proof uses only (36), and µ = ⌈ln(3/η)⌉ there
--   - encoding: V_fin can be coupled with G so that Pr[|√µ V_fin − G| > ξ] ≤ η → IsComplexGaussianSampler (√µ) ξ η (finPoissonSampler K_max q thr); reason: Definition 3.1 is exactly this coupling condition
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Lemma 4.3, (38)–(39), p.20–21; proof p.21

import Mathlib
import Definitions.Def_QNatProofs_finPoissonSampler

set_option autoImplicit false

namespace QNatProofs

/-- **Lemma 4.3 (Finite sampler approximation)** (Li, Parham, *Natural proofs for quantum state
preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.20–21): "For any
approximation error `ξ ∈ (0, 1)` and failure probability `η ∈ (0, 1)`, there exist sampler
parameters `µ`, `K_max`, and `q` satisfying `µ, K_max, q = O(log(2/ξ) + log(2/η))`, (38) such that
the output `V_fin` of the finite Poisson sampler can be coupled with `G ∼ N_ℂ(0, 1)` so that
`Pr[|√µ V_fin − G| > ξ] ≤ η`. (39)"

**Formalization Note** `O(·)` is one absolute constant `c` for all `ξ, η`. The Poisson mean is a
natural number `µ ≥ 1`. The coupling holds for every admissible choice (36) of the thresholds; it
is stated as `IsComplexGaussianSampler √µ ξ η` (Definition 3.1). -/
theorem lemma_4_3 : ∃ c : ℝ, ∀ ξ η : ℝ, 0 < ξ → ξ < 1 → 0 < η → η < 1 →
    ∃ mu Kmax q : ℕ, 1 ≤ mu ∧
      (mu : ℝ) ≤ c * (Real.log (2 / ξ) + Real.log (2 / η)) ∧
      (Kmax : ℝ) ≤ c * (Real.log (2 / ξ) + Real.log (2 / η)) ∧
      (q : ℝ) ≤ c * (Real.log (2 / ξ) + Real.log (2 / η)) ∧
      ∀ thr : ℕ → ℕ, AdmissibleThresholds mu Kmax q thr →
        IsComplexGaussianSampler (Real.sqrt mu) ξ η (finPoissonSampler Kmax q thr) := by sorry

end QNatProofs
