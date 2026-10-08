-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_lemma_8_7
-- name    : SmallGainISS.OmegaPath.lemma_8_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:06.864846+00:00
-- url     : https://prove2.me/theorems/04695ded-b35f-4d76-aa99-0ea97dfadc53
-- title:
--   Lemma 8.7 — $T^{k+1}(\Psi)\subset T^k(\Psi)$, and $\Psi(D\circ T)\cap\{s>0\}\subset\Omega(T)$
-- statement:
--   Let $T:\mathbb R^n_+\to\mathbb R^n_+$ be continuous and monotone ($x\le y\Rightarrow T(x)\le T(y)$; continuity is the standing assumption of §8.1, p. 22), and let $D=\mathrm{diag}(\rho)$ with $\rho\in\mathcal K_\infty$, $\rho>\mathrm{id}$. Write $\Psi(S)=\{s:S(s)\le s\}$ and $\Omega(S)=\{s:S(s)<s\}$. Then
--
--   1. $T^{k+1}(\Psi(T))\subset T^k(\Psi(T))$ for all $k\ge0$;
--   2. if $T$ is strictly increasing ($v<w\Rightarrow T(v)<T(w)$), then
--   $$\Psi(D\circ T)\cap\{s\in\mathbb R^n_+:s>0\}\subset\Omega(T),\qquad \Psi(T\circ D)\cap\{s\in\mathbb R^n_+:s>0\}\subset\Omega(T).$$
--
--   Part 1 makes $\Psi_\infty(T)$ a decreasing intersection; part 2 turns points of a decay set of the scaled operator into points of $\Omega$, which is how Theorem 8.11 lands in $\Omega(\Gamma_\mu)$.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 23, Lemma 8.7

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- Lemma 8.7 (p. 23). Let `T : ℝⁿ₊ → ℝⁿ₊` be continuous and monotone
(the standing assumption of §8.1, p. 22) and `D = diag(ρ)`, `ρ ∈ 𝒦∞`, `ρ > id`.
(i) `Tᵏ⁺¹(Ψ) ⊂ Tᵏ(Ψ)` for all `k ≥ 0`;
(ii) if `T(v) < T(w)` whenever `v < w`, then `Ψ(D ∘ T) ∩ {s > 0} ⊂ Ω(T)` and
`Ψ(T ∘ D) ∩ {s > 0} ⊂ Ω(T)`. -/
theorem lemma_8_7 {n : ℕ} (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0)) (hT : Monotone T)
    (hcont : Continuous T)
    (ρ : ℝ≥0 → ℝ≥0) (hρ : SmallGainISS.Lyapunov.IsKInf ρ) (hρid : GtId ρ) :
    (∀ k : ℕ, T^[k + 1] '' Psi T ⊆ T^[k] '' Psi T) ∧
    (StrictlyIncreasingOp T →
      Psi (diagOp ρ ∘ T) ∩ {s | SPos s} ⊆ SmallGainISS.Lyapunov.Omega T ∧
      Psi (T ∘ diagOp ρ) ∩ {s | SPos s} ⊆ SmallGainISS.Lyapunov.Omega T) := by sorry

end SmallGainISS.OmegaPath
