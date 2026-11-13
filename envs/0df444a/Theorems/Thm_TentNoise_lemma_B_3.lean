-- Prove2me | Theorems.Thm_TentNoise_lemma_B_3
-- name    : TentNoise.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:43:25.548046+00:00
-- url     : https://prove2.me/theorems/6dd715c5-2869-439f-8517-b89722548dc8
-- title:
--   Lemma B.3 — the fitted map: prediction error $\sqrt2\,b/(\pi N)$ and reverse branch probabilities $\tfrac12\pm u'$
-- statement:
--   Fix an integer $N\ge1$ and $0<b\le1/32$, and set $u(y)=\frac{b}{\pi N}\sin(\pi Ny)$, $h_0(y)=\frac y2+u(y)$, $h_1(y)=1-\frac y2+u(y)$. Then
--
--   $$
--   g(x)=\begin{cases}h_0^{-1}(x),&0\le x\le\tfrac12,\\ h_1^{-1}(x),&\tfrac12\le x\le1\end{cases}
--   $$
--
--   defines a continuous map of $[0,1]$ into itself that preserves $\mu$. It is uniformly expanding on each branch and satisfies $\mathrm{Lip}(g)<3$. Its errors are
--
--   $$
--   \delta:=\|g-f\|_{L^2(\mu)}=\frac{\sqrt2\,b}{\pi N},\qquad \|g-f\|_\infty=\frac{2b}{\pi N},
--   $$
--
--   and its stationary reverse kernel is
--
--   $$
--   R_u(y)=p_0(y)\,\delta_{h_0(y)}+p_1(y)\,\delta_{h_1(y)},\qquad p_0=\tfrac12+u',\ p_1=\tfrac12-u'.
--   $$
--
--   The prediction error is of order $b/N$ while the branch probabilities move by order $b$: a small error in $g$ with a large effect on the reverse dynamics.
--
--   **Formalization Note** The map is any $g$ with $g(h_0(y))=g(h_1(y))=y$ for $y\in[0,1]$, which determines it on $[0,1]$; the first clause states that such a $g$ exists. "Uniformly expanding on each branch" is a common factor $\lambda>1$ with $|g(x)-g(y)|\ge\lambda|x-y|$ on $[0,\tfrac12]$ and on $[\tfrac12,1]$; $\mathrm{Lip}(g)<3$ is a Lipschitz constant $K<3$ on $[0,1]$; $\|g-f\|_\infty$ is the maximum of $|g-f|$ on $[0,1]$; the reverse kernel is stated as the joint law of $(g(X),X)$, $X\sim\mu$, namely $\mu\otimes R_u$.
--
--   Differences from the source:
--   - encoding: g defined piecewise by the inverses h_0⁻¹, h_1⁻¹ on [0,1] → ∃ g with IsFitMap N b g, and the properties for every g with IsFitMap N b g (g ∘ h_0 = g ∘ h_1 = id on [0,1]); reason: h_0, h_1 are bijections onto [0,1/2], [1/2,1], so the predicate pins g down on [0,1]; values off [0,1] are unused
--   - encoding: continuous uniform-measure-preserving map, Lip(g) < 3, uniformly expanding on each branch → ContinuousOn g [0,1], g([0,1]) ⊆ [0,1], µ.map g = µ, ∃ K < 3 LipschitzOnWith K g [0,1], ∃ λ > 1 expanding on [0,1/2] and on [1/2,1]; reason: direct transcription on the state space [0,1]
--   - encoding: ‖g − f‖_∞ = 2b/(πN) → 2b/(πN) is the greatest value of |g − f| on [0,1]; reason: g − f is continuous on the compact [0,1], so its sup norm is a maximum
--   - encoding: stationary reverse kernel R_u → joint law of (g(X), X), X ∼ µ, equals µ ⊗ R_u; reason: this is what 'stationary reverse kernel' means: the conditional law of X given g(X) = y
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma B.3, pp.26–27 (PDF pp.26–27), eqs. (60)–(61)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_unifI
import Definitions.Def_TentNoise_errP
import Definitions.Def_TentNoise_IsFitMap
import Definitions.Def_TentNoise_revKernelFit

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Lemma B.3 (Prediction error and reverse branch probabilities)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma B.3,
pp.26–27, eqs. (60)–(61)): fix an integer `N ≥ 1` and `0 < b ≤ 1/32`, and set
`u(y) = (b/(πN)) sin(πNy)`, `h₀(y) = y/2 + u(y)`, `h₁(y) = 1 − y/2 + u(y)`. Then
`g = h₀⁻¹` on `[0, 1/2]`, `g = h₁⁻¹` on `[1/2, 1]` defines a continuous, uniform-measure-preserving
map, uniformly expanding on each branch, with `Lip(g) < 3`; its errors are
`δ := ‖g − f‖_{L²(µ)} = √2 b/(πN)` and `‖g − f‖_∞ = 2b/(πN)`; its stationary reverse kernel is
`R_u(y) = p₀(y) δ_{h₀(y)} + p₁(y) δ_{h₁(y)}`, `p₀ = 1/2 + u′`, `p₁ = 1/2 − u′`.

**Formalization Note** The map is any `g` with `IsFitMap N b g` (`g ∘ h₀ = g ∘ h₁ = id` on `[0, 1]`),
which pins `g` down on `[0, 1]`; the first conjunct states that such a `g` exists. "Uniformly expanding
on each branch" is a common factor `λ > 1` with `|g x − g y| ≥ λ|x − y|` on `[0, 1/2]` and on `[1/2, 1]`.
`Lip(g) < 3` is a Lipschitz constant `K < 3` on `[0, 1]`. `‖g − f‖_∞` is the maximum of `|g − f|` on
`[0, 1]` (`IsGreatest`). The reverse kernel is stated as the joint law of `(g(X), X)`, `X ∼ µ`:
`µ ⊗ R_u`. -/
theorem lemma_B_3 (N : ℕ) (hN : 1 ≤ N) (b : ℝ) (hb0 : 0 < b) (hb : b ≤ 1 / 32) :
    (∃ g : ℝ → ℝ, IsFitMap N b g) ∧
    ∀ g : ℝ → ℝ, IsFitMap N b g →
      ContinuousOn g (Icc 0 1) ∧
      MapsTo g (Icc (0 : ℝ) 1) (Icc 0 1) ∧
      unifI.map g = unifI ∧
      (∃ lam : ℝ, 1 < lam ∧
        (∀ x ∈ Icc (0 : ℝ) (1 / 2), ∀ y ∈ Icc (0 : ℝ) (1 / 2), lam * |x - y| ≤ |g x - g y|) ∧
        (∀ x ∈ Icc (1 / 2 : ℝ) 1, ∀ y ∈ Icc (1 / 2 : ℝ) 1, lam * |x - y| ≤ |g x - g y|)) ∧
      (∃ K : ℝ≥0, (K : ℝ) < 3 ∧ LipschitzOnWith K g (Icc (0 : ℝ) 1)) ∧
      errP g = Real.sqrt 2 * b / (Real.pi * N) ∧
      IsGreatest ((fun x => |g x - tentMap 2 x|) '' Icc 0 1) (2 * b / (Real.pi * N)) ∧
      unifI.map (fun x => (g x, x)) = unifI ⊗ₘ revKernelFit N b := by sorry

end TentNoise
