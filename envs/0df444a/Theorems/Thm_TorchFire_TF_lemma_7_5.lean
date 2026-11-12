-- Prove2me | Theorems.Thm_TorchFire_TF_lemma_7_5
-- name    : TorchFire.TF.lemma_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:47:31.679935+00:00
-- url     : https://prove2.me/theorems/8662220e-cf23-4c71-9bc6-91dad09fe9be
-- title:
--   Lemma 7.5 — $\Pr[\mathrm{TF.Setup}\text{ aborts}]\le\binom R2 2^{-rL}=\mathrm{negl}(\lambda)$
-- statement:
--   The setup of Construction 7.4 aborts precisely when two of the $R$ independently and uniformly sampled torch keys $t_j\in(\{0,1\}^r)^L$ coincide. Its probability satisfies
--   $$\Delta_{\mathrm{setup}}:=\Pr[\mathrm{TF.Setup}^O\text{ aborts}]\le\binom R2 2^{-rL}\quad(49),$$
--   and this is negligible in $\lambda$ for polynomially bounded $R$.
--
--   Differences from the source:
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - encoding: negl(λ) and polynomials → ν ≥ 0 with ν(λ) ≤ λ^{−c} eventually for every c > 0; p(λ) ≤ (λ+2)^c (published PPADSIS.SubexpSIS definitions); reason: paper.md decision 8; equivalent to p.16 for nonnegative ν
--   - reading: TF.GenOracles(1^λ) (Definition 6.1) → TF.GenOracles(1^λ, 1^R) (Construction 7.4 item 1); reason: paper.md decision 11: the oracle T publishes the R torch keys
--   - encoding: "Fix the oracles, published torch keys, and an honest spark serial"; probability over the torch keys → average over the whole oracle sample; reason: the abort depends only on the torch keys, which are independent of the other samples
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Lemma 7.5, (49), p.54

import Mathlib
import Definitions.Def_TorchFire_TF_cloneTF
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS PPADSIS.SubexpSIS

namespace TorchFire.TF

/-- **Lemma 7.5**, (49), p.54 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593). The probability over the torch keys that `TF.Setup^O` aborts
(two of the `R` independently sampled keys coincide) satisfies
`Δ_setup := Pr[TF.Setup^O aborts] ≤ (R choose 2) 2^{−rL}`, and this is negligible for polynomially
bounded `R`. -/
theorem lemma_7_5 :
    (∀ lam R : ℕ, avg (Sample lam R) (fun ω => if SetupOK ω then 0 else 1) ≤
      (R.choose 2 : ℝ) * (2 : ℝ)⁻¹ ^ (r lam * L lam)) ∧
    ∀ R : ℕ → ℕ, PolyBounded R →
      Negligible fun lam => avg (Sample lam (R lam)) (fun ω => if SetupOK ω then 0 else 1) := by sorry

end TorchFire.TF
