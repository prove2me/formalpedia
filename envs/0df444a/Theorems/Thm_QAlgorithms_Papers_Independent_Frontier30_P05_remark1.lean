-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P05_remark1
-- name    : QAlgorithms.Papers.Independent.Frontier30.P05.remark1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:12:14.633546+00:00
-- url     : https://prove2.me/theorems/4be3527d-ae39-4eae-8a3e-84029b4e1bc4
-- title:
--   Monotonicity and vanishing of the AFW continuity modulus
-- statement:
--   Let $H$ satisfy the Hamiltonian and partition-trace assumptions of Proposition 1. Let $G$ be an admissible majorant of its actual shifted entropy capacity $\bar F_H$: it is continuous on $[0,\infty)$, majorizes $\bar F_H$ for positive arguments, satisfies $G(x)=o(\sqrt x)$, is strictly increasing on $(0,\infty)$, and $G(x)/\sqrt x$ is nonincreasing. Let $d_0$ be the least positive integer with $\ln d_0>G(0)$, and let $\gamma(d)=G^{-1}(\ln d)$ on the inverse's actual range. For nonnegative real constants $C,D$, define $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$, and
--
--   $$
--   \operatorname{CB}_t(\bar E,\varepsilon\mid C,D)=C\varepsilon(1+4t)\left[G\left(\frac{\bar E}{(\varepsilon t)^2}\right)+\frac1{d_0}+\ln2\right]+D\bigl[2g(\varepsilon t)+g(\varepsilon(1+2t))\bigr].
--   $$
--
--   For positive energy excess $\bar E$ and error $\varepsilon$, admissibility means $0<t\le\varepsilon^{-1}\min\{1,\sqrt{\bar E/\gamma(d_0)}\}$. For fixed $t$, the displayed expression is nondecreasing separately in $\varepsilon$ and $\bar E$ wherever $t$ is admissible at both compared arguments. For every fixed $\bar E>0$, $C,D\ge0$ and $t>0$,
--
--   $$
--   \lim_{\varepsilon\downarrow0}\operatorname{CB}_t(\bar E,\varepsilon\mid C,D)=0.
--   $$
--
--   For fixed positive $t$, admissibility holds at every sufficiently small positive $\varepsilon$. This gives a genuine continuity modulus for the bound in Theorem 1.
-- source:
--   Advanced Alicki-Fannes-Winter method for energy-constrained quantum systems and its use, arXiv:1907.02458v3, PDF p. 10, Remark 1

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P05

noncomputable section

open Filter

open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Frontier30.P05

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.10, Remark 1. Both monotonicities refer to the expression (27),
with the same fixed t wherever it is admissible. For fixed positive t the
admissible interval contains all sufficiently small positive epsilon. The
last clause is the genuine right-hand limit, not a chosen sequence of errors. -/
theorem remark1 (b : HilbertBasis ℕ ℂ H) (S : EnergySpectrum)
    (h14 : Condition14 S) (G : ℝ → ℝ) (hG : AdmissibleMajorant b S G)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    (∀ Ebar t : ℝ, 0 < Ebar → 0 < t →
      ∀ epsilon1 epsilon2 : ℝ, 0 < epsilon1 → epsilon1 ≤ epsilon2 →
        t ≤ parameterLimit G Ebar epsilon1 → t ≤ parameterLimit G Ebar epsilon2 →
        continuityBound G Ebar epsilon1 C D t ≤ continuityBound G Ebar epsilon2 C D t) ∧
    (∀ epsilon t : ℝ, 0 < epsilon → 0 < t →
      ∀ Ebar1 Ebar2 : ℝ, 0 < Ebar1 → Ebar1 ≤ Ebar2 →
        t ≤ parameterLimit G Ebar1 epsilon → t ≤ parameterLimit G Ebar2 epsilon →
        continuityBound G Ebar1 epsilon C D t ≤ continuityBound G Ebar2 epsilon C D t) ∧
    (∀ Ebar t : ℝ, 0 < Ebar → 0 < t →
      Tendsto (fun epsilon : ℝ => continuityBound G Ebar epsilon C D t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P05

end
