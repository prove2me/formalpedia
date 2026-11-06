-- Prove2me | Theorems.Thm_RankOneSK_lemma_4_2
-- name    : RankOneSK.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:57.449486+00:00
-- url     : https://prove2.me/theorems/d01a9b30-8fc0-4225-aa62-8c6e39f318a0
-- title:
--   Lemma 4.2 — Taylor expansions in $\bar J$ of twelve two-spin moments, uniformly in the fields
-- statement:
--   Let $\mu_{J,a,b}$ be the two-spin Ising measure, $\bar J=\tanh J$, $\bar X_0=\tanh a$, $\bar Y_0=\tanh b$, $\sigma_{X_0}=\sqrt{1-\bar X_0^2}$, $\sigma_{Y_0}=\sqrt{1-\bar Y_0^2}$, $\varphi(X)=(X-\bar X_0)/\sigma_{X_0}$, $\varphi(Y)=(Y-\bar Y_0)/\sigma_{Y_0}$, $R_X=(X-\bar X(y))/\sigma_{X_0}$, $R_Y=(Y-\bar Y(x))/\sigma_{Y_0}$ and $M=(x+s\bar X(y))(y+s\bar Y(x))$. All expectations are under $\mu_{J,a,b}$.
--
--   **Lemma 4.2.** There is an absolute constant $K$ such that for all $0\le s\le1$, all $a,b\in\mathbb R$ and all $J$ with $|\bar J|\le\tfrac12$, each of the following holds with $\pm O(t)$ meaning an error of absolute value at most $Kt$:
--   1. $\mathbb E[\varphi(X)^2]=1-2\bar J\bar X_0\bar Y_0\pm O(\bar J^2)$ and $\mathbb E[\varphi(Y)^2]=1-2\bar J\bar X_0\bar Y_0\pm O(\bar J^2)$;
--   2. $\mathbb E[R_X^2]=1\pm O(|\bar J|)$ and $\mathbb E[R_Y^2]=1\pm O(|\bar J|)$;
--   3. $\mathbb E[R_XR_Y]=-\sigma_{X_0}\sigma_{Y_0}\bar J+2\bar X_0\bar Y_0\sigma_{X_0}\sigma_{Y_0}\bar J^2\pm O(|\bar J|^3)$;
--   4. $\mathbb E[R_XR_Y\varphi(X)]=\pm O(\bar J^2)$ and $\mathbb E[R_XR_Y\varphi(Y)]=\pm O(\bar J^2)$;
--   5. $\mathbb E[R_XR_Y\varphi(X)\varphi(Y)]=1\pm O(\bar J^2)$;
--   6. $\mathbb E[MR_XR_Y]=\sigma_{X_0}\sigma_{Y_0}-(s+1)^2\bar X_0\bar Y_0\sigma_{X_0}\sigma_{Y_0}\bar J\pm O(\bar J^2)$;
--   7. $\mathbb E[MR_XR_Y\varphi(X)]=(s-1)\bar X_0\sigma_{Y_0}\pm O(|\bar J|)$ and $\mathbb E[MR_XR_Y\varphi(Y)]=(s-1)\bar Y_0\sigma_{X_0}\pm O(|\bar J|)$;
--   8. $\mathbb E[MR_XR_Y\varphi(X)\varphi(Y)]=(s-1)^2\bar X_0\bar Y_0\pm O(|\bar J|)$.
--
--   These are the entries of the matrix $A$ of Lemma 4.1 to leading order. Lemma 5.2 on p.30 repeats the statement word for word.
--
--   Differences from the source:
--   - reading: standing assumptions of §5 (p.28): |J̄| ⩽ 1/2 and 0 ⩽ s ⩽ 1 → hypotheses |tanh J| ⩽ 1/2 and 0 ⩽ s ⩽ 1; reason: the section states them once at its top
--   - encoding: ± O(·) in each clause → |lhs − main term| ⩽ K·(·) with one absolute K chosen before s, a, b, J; reason: meaning of O(·) with an absolute constant
--   - encoding: J̄ = tanh J with |J̄| ⩽ 1/2 → raw J with |tanh J| ⩽ 1/2, J̄ := tanh J; reason: tanh is a bijection ℝ → (−1, 1)
--   - encoding: x, y ∈ {±1}; expectations under µ_{J,a,b} → Bool spins read as ±1; twoSpinExp J a b; reason: Lean convention; same objects
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Lemma 4.2, p.26 (PDF p.27) = Lemma 5.2, p.30; standing assumptions |J̄| ⩽ 1/2 and 0 ⩽ s ⩽ 1, p.28

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_twoSpinExp
import Definitions.Def_RankOneSK_resX
import Definitions.Def_RankOneSK_resY
import Definitions.Def_RankOneSK_phi
import Definitions.Def_RankOneSK_rankOneM

open OAI.SKGap MeasureTheory ProbabilityTheory Filter

namespace RankOneSK

/-- **Lemma 4.2 (Taylor expansion lemma).** With `J̄ = tanh J`, all expectations under `µ_{J,a,b}`:
(i) `E[φ(X)²] = 1 − 2J̄X̄₀Ȳ₀ ± O(J̄²)`, `E[φ(Y)²] = 1 − 2J̄X̄₀Ȳ₀ ± O(J̄²)`;
(ii) `E[R_X²] = 1 ± O(|J̄|)`, `E[R_Y²] = 1 ± O(|J̄|)`;
(iii) `E[R_X R_Y] = −σ_{X₀}σ_{Y₀}J̄ + 2X̄₀Ȳ₀σ_{X₀}σ_{Y₀}J̄² ± O(|J̄|³)`;
(iv) `E[R_X R_Y φ(X)] = ±O(J̄²)`, `E[R_X R_Y φ(Y)] = ±O(J̄²)`;
(v) `E[R_X R_Y φ(X)φ(Y)] = 1 ± O(J̄²)`;
(vi) `E[M R_X R_Y] = σ_{X₀}σ_{Y₀} − (s + 1)²X̄₀Ȳ₀σ_{X₀}σ_{Y₀}J̄ ± O(J̄²)`;
(vii) `E[M R_X R_Y φ(X)] = (s − 1)X̄₀σ_{Y₀} ± O(|J̄|)`, `E[M R_X R_Y φ(Y)] = (s − 1)Ȳ₀σ_{X₀} ± O(|J̄|)`;
(viii) `E[M R_X R_Y φ(X)φ(Y)] = (s − 1)²X̄₀Ȳ₀ ± O(|J̄|)`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Lemma 4.2, p.26 (repeated as Lemma 5.2, p.30); standing assumptions `|J̄| ⩽ 1/2`, `0 ⩽ s ⩽ 1`
of §5, p.28.

**Formalization Note** Two-spin objects: spins are `Bool` read as ±1 by `spinValue`; `twoSpinExp J a b` is
`E_{µ_{J,a,b}}` and `twoSpinExp 0 a b` is `E_{µ_{0,a,b}}`. `X̄₀ = tanh a`, `Ȳ₀ = tanh b`, `σ_{X₀} = √(1 − X̄₀²)`,
`σ_{Y₀} = √(1 − Ȳ₀²)`; `R_X = resX J a b`, `R_Y = resY J a b`, `M = rankOneM J a b s`. Each `± O(·)` is
`|lhs − main term| ⩽ K·(·)` with one absolute `K` chosen before `s, a, b, J`. -/
theorem lemma_4_2 :
    ∃ K : ℝ, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ a b J : ℝ, |Real.tanh J| ≤ 1 / 2 →
      let Jb := Real.tanh J
      let X0 := Real.tanh a
      let Y0 := Real.tanh b
      let σX := Real.sqrt (1 - X0 ^ 2)
      let σY := Real.sqrt (1 - Y0 ^ 2)
      let E := twoSpinExp J a b
      let RX := resX J a b
      let RY := resY J a b
      let M := rankOneM J a b s
      -- (i)
      |E (fun x _ => phi a x ^ 2) - (1 - 2 * Jb * X0 * Y0)| ≤ K * Jb ^ 2 ∧
      |E (fun _ y => phi b y ^ 2) - (1 - 2 * Jb * X0 * Y0)| ≤ K * Jb ^ 2 ∧
      -- (ii)
      |E (fun x y => RX x y ^ 2) - 1| ≤ K * |Jb| ∧
      |E (fun x y => RY x y ^ 2) - 1| ≤ K * |Jb| ∧
      -- (iii)
      |E (fun x y => RX x y * RY x y) - (-(σX * σY * Jb) + 2 * X0 * Y0 * σX * σY * Jb ^ 2)|
        ≤ K * |Jb| ^ 3 ∧
      -- (iv)
      |E (fun x y => RX x y * RY x y * phi a x)| ≤ K * Jb ^ 2 ∧
      |E (fun x y => RX x y * RY x y * phi b y)| ≤ K * Jb ^ 2 ∧
      -- (v)
      |E (fun x y => RX x y * RY x y * phi a x * phi b y) - 1| ≤ K * Jb ^ 2 ∧
      -- (vi)
      |E (fun x y => M x y * RX x y * RY x y) - (σX * σY - (s + 1) ^ 2 * X0 * Y0 * σX * σY * Jb)|
        ≤ K * Jb ^ 2 ∧
      -- (vii)
      |E (fun x y => M x y * RX x y * RY x y * phi a x) - (s - 1) * X0 * σY| ≤ K * |Jb| ∧
      |E (fun x y => M x y * RX x y * RY x y * phi b y) - (s - 1) * Y0 * σX| ≤ K * |Jb| ∧
      -- (viii)
      |E (fun x y => M x y * RX x y * RY x y * phi a x * phi b y) - (s - 1) ^ 2 * X0 * Y0|
        ≤ K * |Jb| := by sorry

end RankOneSK
