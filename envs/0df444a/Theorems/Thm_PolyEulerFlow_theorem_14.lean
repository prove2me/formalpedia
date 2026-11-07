-- Prove2me | Theorems.Thm_PolyEulerFlow_theorem_14
-- name    : PolyEulerFlow.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:29.387191+00:00
-- url     : https://prove2.me/theorems/77eea17f-1fbd-49e3-b3d5-0b01f2ae9e8c
-- title:
--   Theorem 14 — quantitative compilation under temporal refinement
-- statement:
--   Fix a separated affine program and an integer $K\ge256$. The compiled field $F_{K}(h,Z)$ of §6.3 and the initialization $c_K(h,C_0)$ (the intended initial section of p.27) are rational polynomials, and there are a compact box and positive constants $A,B,r^*,c_-\le c_+,s_0$, together with the constants of the $O(\cdot)$ bounds, such that the following holds. Let $h=2^{-s}$, $s\ge s_0$, $\varepsilon=h^K$, $0\le\nu\le\varepsilon^2$, and
--   $$\Delta_\varepsilon=(1+\log(1/\varepsilon))(\varepsilon^{1/4}+\nu).\tag{5}$$
--   For a valid prefix $C_0,\dots,C_T$ of $T\ge1$ transitions with interval gain bound $\Gamma$, suppose
--   $$B\Gamma T\Delta_\varepsilon\le r^*h.\tag{6}$$
--   Starting exactly at the initialization, every trajectory $Z_{k+1}=Z_k+\eta_kF_K(h,Z_k)+\eta_k\xi_k$ with $0<\eta_k\le1$, $\sum_k\eta_k=\infty$, $\|\xi_k\|_\infty\le\nu$ has internal cycle sections $t_{4j}$, $0\le j\le T$, with
--   $$\|Y(t_{4j})-C_j\|_\infty\le B\Gamma j\Delta_\varepsilon,\tag{7}$$
--   $$c_-(1+s)\le t_{4j+4}-t_{4j}\le c_+(1+s)\quad(j<T);\tag{8}$$
--   at each section the state is admissible above $C_j$ (shadow discrepancy at most $A\Delta_\varepsilon$, clock and comparator-cone conditions restored); the prefix stays in the box and has active length $O((1+s)T)$. If the last transition is a resetting halt, every subsequent cycle is admissible and the data stay $O(\Delta_\varepsilon)$-close to $C_T$ at every subsequent update; and the exact flow ($\nu=0$) from the initialization exists and every such solution keeps its data $O(\Delta_\varepsilon)$-close to $C_T$ from time $c_+(1+s)T$ on. All constants are independent of the prefix, the input, the mesh and the disturbances.
--
--   This is the general interface of the compiler: Theorem 1 is the case of the two-stack normal form, with $\Gamma=G/h$ from Lemma 25.
--
--   Differences from the source:
--   - generalization: there are a rational polynomial field F_{M,K} and initialization c_{M,K} → the explicit compiled field of §6.3 and the intended initial section, together with their being rational polynomials; reason: the paper's field is this one ('given explicitly in Section 6.3', p.9), so the statement implies the existential
--   - reading: the clock and comparator-cone conditions are restored; shadow discrepancy at most A∆ε → admissibility (36) above C_j at every section j ≤ T, with the entry constants of Lemma 31 existential jointly; reason: (36) is exactly these conditions (p.10: 'this is the comparator-cone condition, see (36)')
--   - reading: internal cycle sections t_{4j} → the phase entries of the four clock bits, every fourth one, starting at index 0; reason: §6.5 and Lemma 16
--   - reading: every subsequent cycle is admissible; O(∆ε)-close at every subsequent update → all phase entries exist, sections j ≥ T are admissible above C_T, and ‖Y − C_T‖ ≤ C_halt∆ε at every index ≥ the section of index T; reason: the last transition ends at section T
--   - reading: the exact polynomial flow gives the same stable decision, with the same bound on physical time → the ν = 0 flow exists, and every solution has ‖Y(t) − C_T‖ ≤ C_halt∆ε for t ≥ c₊(1+s)T; reason: c₊(1+s)T bounds the time of the halting section by (8); 'decision' is closeness to the halting configuration
--   - encoding: every trajectory with constant η, and the same conclusions for variable steps → every admissible variable mesh; reason: a constant step in (0, 1] is an admissible mesh, so both printed cases are covered
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Theorem 14, p.10 (PDF 12)

import Mathlib
import Definitions.Def_PolyEulerFlow_IsCycleConstants
import Definitions.Def_PolyEulerFlow_IsForcedSolution

namespace PolyEulerFlow

/-- **Theorem 14 (Quantitative compilation under temporal refinement)**, p.10 (PDF 12). Bournez, One Polynomial Field for Every Euler Step and
the Flow (manuscript, sha256 c4e01b2b…).

Fix a separated affine program and an integer `K ≥ 256`. The compiled field `F(h, Z)` of §6.3 and the initialization `c(h, C₀)` (the intended
initial section, p.27) are rational polynomials, and there are a compact box and positive constants `A, B, r∗, c₋, c₊, s₀` (and the constants of the
`O(·)` bounds) such that, for `h = 2^{-s}`, `s ≥ s₀`, `ε = h^K`, `0 ≤ ν ≤ ε²`, `∆ε = (1 + log(1/ε))(ε^{1/4} + ν)` (5), and a valid prefix
`C₀, …, C_T` (`T ≥ 1`) with interval gain bound `Γ` and `BΓT∆ε ≤ r∗h` (6), every trajectory from the initialization with steps `0 < η_k ≤ 1`,
`Σ η_k = ∞`, and update noise `η_kξ_k`, `‖ξ_k‖∞ ≤ ν`, has internal cycle sections `t_{4j}`, `0 ≤ j ≤ T`, with (7) `‖Y(t_{4j}) - C_j‖∞ ≤ BΓj∆ε`,
(8) `c₋(1+s) ≤ t_{4j+4} - t_{4j} ≤ c₊(1+s)` for `j < T`, the shadow discrepancy at most `A∆ε` and the clock and comparator-cone conditions
restored at each section, the prefix in the fixed box with active length `O((1+s)T)`. If the last transition resets to a fixed halting
configuration, every subsequent cycle is admissible and the data stay `O(∆ε)`-close to it at every subsequent update; and the exact flow gives the
same stable decision, with the same bound on physical time. All constants are independent of the prefix, the input, the mesh and the disturbances.

**Formalization Note** The field is the explicit compiled field of §6.3 ("given explicitly in Section 6.3", p.9), together with the statement that it
is a rational polynomial in `(h, Z)`; this implies the printed existential. Sections are the phase entries of the clock bits (every fourth one); "the
clock and comparator-cone conditions are restored" is admissibility (36) at each section, with the entry constants of Lemma 31. "The exact flow
gives the same stable decision, with the same bound on physical time" is read as: the `ν = 0` flow from the initialization exists, and every such
solution has its data within `O(∆ε)` of `C_T` at every time `t ≥ c₊(1+s)T`, the bound (8) gives on the completion of the halting cycle. The variable
mesh contains every constant step `0 < η ≤ 1`. -/
theorem theorem_14 :
    ∃ A0 B0 Cdur Cenv Cnext Dclk ε0 : ℝ, IsUniformClock A0 B0 Cdur Cenv Cnext Dclk ε0 ∧
    ∀ (m g : ℕ) (prog : SeparatedAffineProgram m g) (K : ℕ), 256 ≤ K →
      (∃ Fpoly : CompiledIdx m g → MvPolynomial (Option (CompiledIdx m g)) ℚ,
        ∀ (h : ℝ) (Z : CompiledState m g) (i : CompiledIdx m g),
          compiledField prog K h Z i = MvPolynomial.aeval (fun v : Option (CompiledIdx m g) => v.elim h Z) (Fpoly i)) ∧
      (∃ cpoly : CompiledIdx m g → MvPolynomial (Option (Fin m)) ℚ,
        ∀ (h : ℝ) (C0 : Fin m → ℝ) (i : CompiledIdx m g),
          initState prog K h C0 i = MvPolynomial.aeval (fun v : Option (Fin m) => v.elim h C0) (cpoly i)) ∧
      ∃ (lo hi : CompiledState m g) (A B rstar cm cp Clen Chalt : ℝ) (s0 : ℕ),
        lo ≤ hi ∧ 0 < A ∧ 0 < B ∧ 0 < rstar ∧ 0 < cm ∧ cm ≤ cp ∧ 0 < Clen ∧ 0 < Chalt ∧ 0 < s0 ∧
        ∀ s : ℕ, s0 ≤ s →
          let h := scale s
          let ε := h ^ K
          ∀ (ν : ℝ) (C : ℕ → Fin m → ℝ) (T : ℕ) (Γ : ℝ), 0 ≤ ν → ν ≤ ε ^ 2 → 1 ≤ T →
            prog.IsValidPrefix h C T → prog.IsGainBound h C T Γ → B * Γ * T * deltaEps ε ν ≤ rstar * h →
            let f := compiledField prog K h
            let Z0 := initState prog K h (C 0)
            (∀ (η : ℕ → ℝ) (ξ : ℕ → CompiledState m g), IsAdmissibleMesh η → IsPermittedDisturbance ν ξ →
              let z := eulerOrbit f Z0 η ξ
              let t := physTime η
              ∃ kk : ℕ → ℕ, IsPhaseEntriesUpTo phaseBit z 0 (4 * T) kk ∧
                (∀ j ≤ T, ‖dataY (z (kk (4 * j))) - C j‖ ≤ B * Γ * j * deltaEps ε ν ∧
                  IsAdmissibleAbove prog K A0 B0 A ν h (C j) (z (kk (4 * j)))) ∧
                (∀ j < T, cm * (1 + s) ≤ t (kk (4 * j + 4)) - t (kk (4 * j)) ∧
                  t (kk (4 * j + 4)) - t (kk (4 * j)) ≤ cp * (1 + s)) ∧
                (∀ k ≤ kk (4 * T), z k ∈ Set.Icc lo hi) ∧
                activeLengthOn z 0 (kk (4 * T)) ≤ Clen * (1 + s) * T ∧
                (prog.IsResettingHaltRun h C T →
                  IsPhaseEntries phaseBit z 0 kk ∧
                  (∀ j, T ≤ j → IsAdmissibleAbove prog K A0 B0 A ν h (C T) (z (kk (4 * j)))) ∧
                  ∀ k, kk (4 * T) ≤ k → ‖dataY (z k) - C T‖ ≤ Chalt * deltaEps ε ν)) ∧
            (prog.IsResettingHaltRun h C T →
              (∃ z : ℝ → CompiledState m g, IsForcedSolution f Z0 (fun _ => 0) z) ∧
              ∀ z : ℝ → CompiledState m g, IsForcedSolution f Z0 (fun _ => 0) z →
                ∀ τ : ℝ, cp * (1 + s) * T ≤ τ → ‖dataY (z τ) - C T‖ ≤ Chalt * deltaEps ε 0) := by sorry

end PolyEulerFlow
