-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_Supplement_eta_lyapunov_properties
-- name    : StochApproxDyn.WeakAPT.Supplement.eta_lyapunov_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:18:10.380499+00:00
-- url     : https://prove2.me/theorems/f42d25f6-2db6-4dce-8777-0abd69ad3975
-- title:
--   Proposition 9.5 (corrected: Dη(x) is real valued) — the averaged function η(x)=∫₀ˡV(Φ₋ₜx)dt is a Lyapounov function repelling from S near Γ
-- statement:
--   Assume the setting of Lemma 9.3: the standing assumptions of §9 with $F$ and $S$ of class $C^r$ ($r\ge1$), the choices $T,N,E^u,\tilde E^u,\varepsilon,N_0,\Pi$ of §9.1, $f=\Phi_T$ and $V(x)=\|x-\Pi(x)\|$. Let $N_1\subseteq N_0$ be a neighbourhood of $\Gamma$ and $\rho>1$ as in Lemma 9.3: $f(x)\in N_0$ and $V(f(x))\ge\rho V(x)$ for $x\in N_1$. There exist a compact neighbourhood $\mathcal N(\Gamma)\subseteq N_1$ of $\Gamma$ and real numbers $l>0$, $\beta>0$ such that
--
--   $$\eta(x)=\int_0^lV(\Phi_{-t}(x))\,dt$$
--
--   admits a right derivative $D\eta(x).h=\lim_{t\downarrow0}(\eta(x+th)-\eta(x))/t$ at every $x\in\mathcal N(\Gamma)$ and:
--
--   1. $\eta$ is $C^r$ on $\mathcal N(\Gamma)\setminus S$;
--   2. for all $x\in\mathcal N(\Gamma)\cap S$, $D\eta(x):\mathbb R^m\to\mathbb R$ is Lipschitz, convex and positively homogeneous;
--   3. if $F$ and $S$ are $C^{1+\alpha}$ for some $0<\alpha\le1$ (the case $r\ge1+\alpha$), then $\eta$ is $C^{1+\alpha}$ on $\mathcal N(\Gamma)\setminus S$, and there are $k>0$ and a neighbourhood $U'$ of $0$ with $\eta(x+v)\ge\eta(x)+D\eta(x)v-k\|v\|^{1+\alpha}$ for all $x\in\mathcal N(\Gamma)$, $v\in U'$;
--   4. there is $c_1>0$ with $\|\nabla\eta(x)\|\ge c_1$ for $x\in\mathcal N(\Gamma)\setminus S$, and $D\eta(x)v\ge c_1\|v-D\Pi(x)v\|$ for $x\in\mathcal N(\Gamma)\cap S$, $v\in\mathbb R^m$;
--   5. $D\eta(x)(u+v)=D\eta(x)v$ for $x\in\mathcal N(\Gamma)\cap S$, $u\in T_xS$, $v\in\mathbb R^m$;
--   6. $D\eta(x).F(x)\ge\beta\,\eta(x)$ for all $x\in\mathcal N(\Gamma)$.
--
--   These are the properties of $\eta$ used in the proof of Theorem 9.1 to turn $\eta(x_n)$ into a nonnegative process that satisfies the hypotheses of Lemmas 9.6 and 9.7.
--
--   **Formalization Note** $D\eta(x).h$ is the limit of the right difference quotient (Lean `rightDirDeriv`); its existence at every point of $\mathcal N(\Gamma)$ is stated, since clauses 3–6 use $D\eta(x)$ at all these points. $\nabla\eta$ is Mathlib's `gradient`, $D\Pi(x)$ its `fderiv`. The projection $\Pi$ is named `Pr` in Lean.
--
--   Differences from the source:
--   - correction: "(ii) … a right derivative $D\eta(x):\mathbb R^m\to\mathbb R^m$" → $D\eta(x):\mathbb R^m\to\mathbb R$; reason: the right derivative of the real function $\eta$ is defined on p. 52 as a real limit, and formulas (35), (36) on p. 54 give real values; the printed $\mathbb R^m$ is a typo.
--   - reading: "$\mathcal N(\Gamma)\subset N_1$", with $N_1$ the set of Lemma 9.3 → $N_1$ and $\rho$ are any pair satisfying the conclusion of Lemma 9.3; reason: Lemma 9.3 only asserts their existence.
--   - reading: "(iii) If $r\ge1+\alpha$" → if $F$ and $S$ are $C^{1+\alpha}$; reason: $r$ is the regularity of $F$ and $S$, and $C^r$ with $r\ge1+\alpha$ means $C^{1+\alpha}$; this also covers integer $r\ge2$.
--   - reading: "(i) $\eta$ is $C^r$" for $r=1+\alpha$ → stated inside clause 3 as $\eta$ being $C^{1+\alpha}$ on $\mathcal N(\Gamma)\setminus S$; reason: $r$ in Lean ranges over $\{1,2,\dots,\infty\}$, so the fractional case is stated with the $C^{1+\alpha}$ hypothesis.
--   - reading: "$D\eta(x)$" used at every $x\in\mathcal N(\Gamma)$ → existence of the right derivative at every point of $\mathcal N(\Gamma)$ is part of the conclusion; reason: clauses (iii)–(vi) presuppose it.
--   - generalization: $F$ and $S$ smooth (standing assumption, p. 47) → $C^r$, $r\ge1$, and $C^{1+\alpha}$ with locally Hölder derivatives; reason: smooth data are the case $r=\infty$, and a globally Hölder derivative is locally Hölder.
--   - correction: the tubular construction uses $S\cap\operatorname{int}N\subseteq N_0\subseteq N$; reason: the printed ambient open subset of $N$ cannot contain boundary points; the construction is local around $\Gamma$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 53, Proposition 9.5 (right derivative, p. 52; formulas (35), (36), p. 54; construction of §9.1 step 1, pp. 50–51; Lemma 9.3, p. 51)

import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_Supplement_NormallyRepelling

open Filter
open scoped NNReal

namespace StochApproxDyn.WeakAPT.Supplement

/-- Proposition 9.5 (Benaïm 1999, p. 53). In the setting of §9, with `F` and `S` of class `C^r`
(`r ≥ 1`), let `T, N, E^u, Ẽ^u, ε, N₀, Π` be chosen as in §9.1, step 1 (pp. 50–51),
`f = Φ_T`, `V(x) = ‖x − Π(x)‖`, and let `N₁ ⊆ N₀`, `ρ > 1` be as in Lemma 9.3
(`f(x) ∈ N₀` and `V(f(x)) ≥ ρ V(x)` for `x ∈ N₁`). There exist a compact neighbourhood
`𝒩(Γ) ⊆ N₁` of `Γ` and real numbers `l > 0`, `β > 0` such that
`η(x) = ∫_0^l V(Φ_{−t}(x)) dt` has a right derivative `Dη(x)` at every `x ∈ 𝒩(Γ)` and:
(i) `η` is `C^r` on `𝒩(Γ) \ S`;
(ii) for all `x ∈ 𝒩(Γ) ∩ S`, the right derivative `Dη(x) : ℝ^m → ℝ` is Lipschitz, convex and
positively homogeneous;
(iii) if `F` and `S` are `C^{1+α}` for some `0 < α ≤ 1` (the case `r ≥ 1 + α`), there are
`k > 0` and a neighbourhood `U'` of `0` with `η(x + v) ≥ η(x) + Dη(x)v − k‖v‖^{1+α}` for all
`x ∈ 𝒩(Γ)`, `v ∈ U'` (and, this being clause (i) for `r = 1 + α`, `η` is `C^{1+α}` on
`𝒩(Γ) \ S`);
(iv) there is `c₁ > 0` with `‖∇η(x)‖ ≥ c₁` for `x ∈ 𝒩(Γ) \ S` and
`Dη(x)v ≥ c₁‖v − DΠ(x)v‖` for `x ∈ 𝒩(Γ) ∩ S`, `v ∈ ℝ^m`;
(v) `Dη(x)(u + v) = Dη(x)v` for `x ∈ 𝒩(Γ) ∩ S`, `u ∈ T_x S`, `v ∈ ℝ^m`;
(vi) `Dη(x).F(x) ≥ β η(x)` for all `x ∈ 𝒩(Γ)`.
The paper prints the codomain of `Dη(x)` in (ii) as `ℝ^m`; it is `ℝ` (definition on p. 52 and
formulas (35), (36)). Here `Pr` is the projection `Π`. -/
theorem eta_lyapunov_properties {m d : ℕ} (r : ℕ∞) (hr : 1 ≤ r)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (hF : ContDiff ℝ (r : WithTop ℕ∞) F)
    (Φ : Flow ℝ (EuclideanSpace ℝ (Fin m))) (S Γ U : Set (EuclideanSpace ℝ (Fin m))) (t₀ : ℝ)
    (hS : IsSubmanifoldOfClass r d S)
    (Eu : EuclideanSpace ℝ (Fin m) → Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    (hNR : IsNormallyRepellingSet d F Φ S Γ U t₀ Eu) (T : ℝ) (N : Set (EuclideanSpace ℝ (Fin m)))
    (Eext Et : EuclideanSpace ℝ (Fin m) → Submodule ℝ (EuclideanSpace ℝ (Fin m))) (ε : ℝ)
    (N₀ : Set (EuclideanSpace ℝ (Fin m)))
    (Pr : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hC : IsTubularConstruction d Φ S Γ U Eu T N Eext Et ε N₀ Pr)
    (N₁ : Set (EuclideanSpace ℝ (Fin m))) (hN₁ : N₁ ∈ nhdsSet Γ) (hN₁₀ : N₁ ⊆ N₀) (ρ : ℝ)
    (hρ : 1 < ρ) (hN₁ρ : ∀ x ∈ N₁, Φ T x ∈ N₀ ∧ ρ * tubeDist Pr x ≤ tubeDist Pr (Φ T x)) :
    ∃ NΓ : Set (EuclideanSpace ℝ (Fin m)), IsCompact NΓ ∧ NΓ ∈ nhdsSet Γ ∧ NΓ ⊆ N₁ ∧
      ∃ l β : ℝ, 0 < l ∧ 0 < β ∧
        (∀ x ∈ NΓ, HasRightDirDerivAt (etaFun Φ Pr l) x) ∧
        -- (i)
        ContDiffOn ℝ (r : WithTop ℕ∞) (etaFun Φ Pr l) (NΓ \ S) ∧
        -- (ii)
        (∀ x ∈ NΓ ∩ S, (∃ L : ℝ≥0, LipschitzWith L (rightDirDeriv (etaFun Φ Pr l) x)) ∧
          ConvexOn ℝ Set.univ (rightDirDeriv (etaFun Φ Pr l) x) ∧
          ∀ c : ℝ, 0 ≤ c → ∀ h, rightDirDeriv (etaFun Φ Pr l) x (c • h) =
            c * rightDirDeriv (etaFun Φ Pr l) x h) ∧
        -- (iii)
        (∀ α : ℝ≥0, 0 < α → α ≤ 1 → IsC1HolderOn α F Set.univ → IsC1HolderSubmanifold α d S →
          IsC1HolderOn α (etaFun Φ Pr l) (NΓ \ S) ∧ ∃ k : ℝ, 0 < k ∧ ∃ U' ∈ nhds (0 : EuclideanSpace ℝ (Fin m)), ∀ x ∈ NΓ, ∀ v ∈ U',
            etaFun Φ Pr l x + rightDirDeriv (etaFun Φ Pr l) x v - k * ‖v‖ ^ (1 + (α : ℝ)) ≤
              etaFun Φ Pr l (x + v)) ∧
        -- (iv)
        (∃ c₁ : ℝ, 0 < c₁ ∧ (∀ x ∈ NΓ \ S, c₁ ≤ ‖gradient (etaFun Φ Pr l) x‖) ∧
          ∀ x ∈ NΓ ∩ S, ∀ v, c₁ * ‖v - fderiv ℝ Pr x v‖ ≤ rightDirDeriv (etaFun Φ Pr l) x v) ∧
        -- (v)
        (∀ x ∈ NΓ ∩ S, ∀ u ∈ tangentSubspace S x, ∀ v,
          rightDirDeriv (etaFun Φ Pr l) x (u + v) = rightDirDeriv (etaFun Φ Pr l) x v) ∧
        -- (vi)
        ∀ x ∈ NΓ, β * etaFun Φ Pr l x ≤ rightDirDeriv (etaFun Φ Pr l) x (F x) := by sorry

end StochApproxDyn.WeakAPT.Supplement
