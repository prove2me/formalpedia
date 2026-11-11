-- Prove2me | Theorems.Thm_QVolKLS_lemma_6_3
-- name    : QVolKLS.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:39:47.8313+00:00
-- url     : https://prove2.me/theorems/eb5ab821-92c3-47f6-b0cc-aaefd9242436
-- title:
--   Lemma 6.3 — $q_{\mathrm{in}}\ge1/2$, $q_{\mathrm{out}}\ge1/(2(e+1))$; query-free $Z_{C,\Lambda}$, $|\nu_\Lambda\rangle$; $|\pi_0\rangle$ with $O(\log(1/\varepsilon_{\mathrm{init}}))$ queries
-- statement:
--   Let $d\ge2$, $D=d+1$, $\kappa>0$; $K\subseteq\mathbb R^d$ ranges over convex bodies with $B(0,1)\subseteq K\subseteq B(0,\kappa)$; $C$ is the cone, $\nu_\Lambda$ its lattice law at $a_0=4D$, and $\pi_0$ the lattice law of the pencil at $a_0$.
--
--   1. **Endpoint probabilities.** There is $h_0>0$ (depending on $d,\kappa$) such that for every spacing $0<h\le h_0$ and every such $K$,
--   $$
--   q_{\mathrm{in}}\ge\tfrac12,\qquad q_{\mathrm{out}}\ge\frac1{2(e+1)} .
--   $$
--   2. **Normalization of the cone.** $\log Z_{C,\Lambda}$ can be computed to any prescribed accuracy with no membership queries: there is a computable function returning, from $d$, a rational $\kappa\ge1$, $p$ (with $h=2^{-p}$) and $j$, a rational within $2^{-j}$ of $\log Z_{C,\Lambda}$.
--   3. **The cone qsample.** For every point-register format covering $C\cap2^{-p}\mathbb Z^D$ and every $\delta>0$, the qsample $|\nu_\Lambda\rangle$ and its controlled reflection can be prepared within $\delta$ by circuits over $\{H,T,\mathrm{CNOT}\}$ with no membership query (workspace returned to $|0\rangle$).
--   4. **Initial qsample.** There is an absolute $C$ and, for each $d,\kappa$, an $h_0>0$ such that for every dyadic $h=2^{-p}\le h_0$, every covering register and every $0<\varepsilon_{\mathrm{init}}<\tfrac12$, one circuit with at most $C\log(1/\varepsilon_{\mathrm{init}})$ membership queries prepares, for every such $K$, a state whose point register is within trace distance $\varepsilon_{\mathrm{init}}$ of $|\pi_0\rangle\langle\pi_0|$.
--
--   These are the initialization and termination guarantees of the cooling schedule.
--
--   **Formalization Note** In clause 4 the circuit uses arbitrary unitary gates (so "given access to $|\nu_\Lambda\rangle$ and its controlled reflection" is automatic: both are independent of $K$) and counts only calls to the membership oracle of $K$, applied to the $d$ coordinates of $z'$; it is chosen before $K$.
--
--   Differences from the source:
--   - encoding: §6.1 standing assumptions: 'Assume d ≥ 2 below' (p.44) and the rescaled body B(0,1) ⊆ K ⊆ B(0,κ) → hypotheses d ≥ 2, IsConvexBody K, Metric.ball 0 1 ⊆ K ⊆ Metric.closedBall 0 κ; reason: they restate the section's setting; balls as in the main theorem
--   - reading: for a sufficiently fine lattice → ∃ h₀ > 0 depending on d and κ such that every spacing h ≤ h₀ works (clause 4: every dyadic h = 2^{-p} ≤ h₀); reason: the stronger reading, uniform in K, as the quadrature bounds of Lemma B.2 are
--   - reading: log Z_{C,Λ} can be computed to any prescribed accuracy with no membership queries → a Computable function of (d, κ, p, j), κ rational ≥ 1 and h = 2^{-p}, within 2^{-j} of log Z_{C,Λ}; reason: 'no membership queries' means a classical computation from the known data; κ ≥ 1 holds under the standing assumptions
--   - reading: the qsample |ν_Λ⟩ and its controlled reflection can be prepared to prescribed accuracy without membership queries → for every δ > 0, circuits over {H, T, CNOT} without oracle calls approximating |0^w⟩|ν_Λ⟩ and the controlled reflection (workspace returned to |0⟩) within δ in norm; reason: the paper's gate set is fixed (§2.4) and the preparation uses no oracle
--   - encoding: given access to |ν_Λ⟩ and its controlled reflection, prepare |π₀⟩ … using O(log(1/ε_init)) membership queries → a circuit over arbitrary unitary gates from |0⟩ with ≤ C·log(1/ε_init) calls to memOracle K b p; trace distance of the reduced point-register state; reason: |ν_Λ⟩ and its reflection do not depend on K, so arbitrary gates give that access; only membership queries are counted, as in the lemma
--   - encoding: qsamples on the lattice points → qsamples on a point register of format (b, p) that represents every lattice point of the cone (RegCovers); reason: the register encodes a box of lattice points (§3.2, p.27)
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Lemma 6.3, p.47 (with (49)–(50), p.45)

import Definitions.Def_QVolKLS_pencil
import Definitions.Def_QVolKLS_fourthMomentNorm
import Definitions.Def_QAlgorithms_Defs_GradientMethods

set_option autoImplicit false

namespace QVolKLS

open QAlgorithms

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Lemma 6.3**, p.47. Standing
assumptions of §6.1 (p.44): `d ≥ 2`, `B(0, 1) ⊆ K ⊆ B(0, κ)`; `C` is the cone, `ν_Λ` its lattice law
at `a₀ = 4D`, `π₀` the lattice law of the pencil at `a₀`, and the lattice is `Λ = hℤ^D`.

1. For a sufficiently fine lattice, `q_in ≥ 1/2` and `q_out ≥ 1/(2(e + 1))`.
2. `log Z_{C,Λ}` can be computed to any prescribed accuracy with no membership queries: a computable
   function of `(d, κ, p, j)` (rational `κ ≥ 1`, `h = 2^{-p}`) returns a rational within `2^{-j}` of
   `log Z_{C,Λ}`.
3. `|ν_Λ⟩` and its controlled reflection can be prepared to any accuracy `δ > 0` with no membership
   queries: by circuits over `{H, T, CNOT}` without oracle calls (with workspace returned to `|0⟩`).
4. With `O(log(1/ε_init))` membership queries one prepares `|π₀⟩` to trace distance `ε_init`, for a
   sufficiently fine lattice and every `0 < ε_init < 1/2`.

**Formalization Note.**
* Qsamples live on a point register of format `(b, p)`, `h = 2^{-p}`, large enough to represent every
  lattice point of the cone (`RegCovers`); `regWeight` places a lattice law on the register labels.
  `qsampleRefl` on the whole register is the reflection `2|ν_Λ⟩⟨ν_Λ| − I` (the paper's
  `U_C(2|0⟩⟨0| − I)U_C†`), and `controlledQubits` adds a control on wire `0`.
* "No membership queries" is read as: in clause 2, a classical computable function of the known data
  (`Computable`, with Mathlib's encoding of `ℕ × ℚ × ℕ × ℕ`), which never sees `K`; in clause 3, a
  plain circuit (`Circuit`) with no oracle at all.
* In clause 4 "given access to `|ν_Λ⟩` and its controlled reflection" is subsumed by arbitrary unitary
  gates (`unitaryGateSet`): the circuit starts from `|0⟩`, may prepare `|ν_Λ⟩` and its reflection
  (they do not depend on `K`), and counts only membership queries (`memOracle K b p` on the `d`
  coordinates of `z′`). It is chosen before `K`. The error is the trace distance between the reduced
  state of the point register (workspace discarded) and `|π₀⟩⟨π₀|`.
* "Sufficiently fine" is: every spacing `h ≤ h₀`, with `h₀` depending on `d` and `κ` only; one
  absolute constant `C` serves clause 4. -/
theorem lemma_6_3 :
    (∀ (d : ℕ), 2 ≤ d → ∀ κ : ℝ, ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h → h ≤ h0 →
      ∀ K : Set (Euc d), IsConvexBody K → Metric.ball 0 1 ⊆ K → K ⊆ Metric.closedBall 0 κ →
        1 / 2 ≤ qIn K κ h ∧ 1 / (2 * (Real.exp 1 + 1)) ≤ qOut K κ h) ∧
    (∃ f : ℕ × ℚ × ℕ × ℕ → ℚ, Computable f ∧
      ∀ (d : ℕ) (κ : ℚ) (p j : ℕ), 1 ≤ κ →
        |((f (d, κ, p, j) : ℚ) : ℝ) - Real.log (coneZLat d (κ : ℝ) ((2 : ℝ)⁻¹ ^ p))| ≤
          (2 : ℝ)⁻¹ ^ j) ∧
    (∀ (d : ℕ), 2 ≤ d → ∀ (κ : ℝ) (p b : ℕ), RegCovers (d + 1) b p (cone d κ) →
      ∀ δ : ℝ, 0 < δ →
        (∃ (w : ℕ) (c : Circuit htcxGateSet (w + (d + 1) * b)),
          jointNorm (fun z => act c.unitary (zeroKet (w + (d + 1) * b)) z -
            withZeroAnc w (qsample (regWeight (d + 1) b p (cone d κ)
              (coneLatLaw d κ ((2 : ℝ)⁻¹ ^ p)))) z) ≤ δ) ∧
        (∃ (w : ℕ) (c : Circuit htcxGateSet (w + ((d + 1) * b + 1))),
          ∀ Φ : Qubits ((d + 1) * b + 1) → ℂ, jointNorm Φ = 1 →
            jointNorm (opApply c.unitary (withZeroAnc w Φ) -
              withZeroAnc w (opApply (controlledQubits (qsampleRefl (regWeight (d + 1) b p
                (cone d κ) (coneLatLaw d κ ((2 : ℝ)⁻¹ ^ p))))) Φ)) ≤ δ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 2 ≤ d → ∀ κ : ℝ, ∃ h0 : ℝ, 0 < h0 ∧
      ∀ (p b : ℕ), (2 : ℝ)⁻¹ ^ p ≤ h0 → RegCovers (d + 1) b p (cone d κ) →
      ∀ εi : ℝ, 0 < εi → εi < 1 / 2 →
        ∃ (a : ℕ) (c : OracleCircuit unitaryGateSet (fun _ : Fin 1 => d * b + 1)
            (a + (d + 1) * b)),
          (c.queryCount 0 : ℝ) ≤ C * Real.log (1 / εi) ∧
          ∀ K : Set (Euc d), IsConvexBody K → Metric.ball 0 1 ⊆ K →
            K ⊆ Metric.closedBall 0 κ →
            traceDist
              (reducedSnd (fun z => act (c.unitary (fun _ => memOracle K b p))
                (zeroKet (a + (d + 1) * b)) z))
              (pureDensity (qsample (regWeight (d + 1) b p (pencil K κ)
                (pencilLatLaw K κ ((2 : ℝ)⁻¹ ^ p) (coolingA d 0))))) ≤ εi) := by sorry

end QVolKLS
