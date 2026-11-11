-- Prove2me | Theorems.Thm_QVolKLS_corollary_5_3
-- name    : QVolKLS.corollary_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:41:32.077281+00:00
-- url     : https://prove2.me/theorems/254270cd-fc5f-480d-8011-e22f8ce6f717
-- title:
--   Corollary 5.3 — lattice qsample reflections to error $\varepsilon_{\mathrm{ref}}$ with $\tilde O(D/\psi)$ membership queries per call
-- statement:
--   Fix the setting of §5.1: a convex body $K\subset\mathbb R^D$ with rational data $x_c,r_0,R_0$ and $B(x_c,r_0)\subseteq K\subseteq B(x_c,R_0)$, rational tilts $b_0,\dots,b_m$, rationals $0<\lambda_-\le\lambda_+$ and $0<\psi\le\psi_D$; $\pi_{b_i}$ is the log-affine law and $\pi_{i,\Lambda}$ its lattice law on $K\cap h\mathbb Z^D$.
--
--   For every comparison constant $c\ge1$ there is $C$ such that for all such data and every $M_4\ge1$, $0<\varepsilon_{\mathrm{ref}}<\tfrac12$:
--
--   - there is a common dyadic spacing $h=2^{-p}$ with $1/h\le C\,\Xi^C$, where $\Xi=D+R_0/r_0+(1+\max_i\|b_i\|)R_0+\lambda_+/\lambda_-+R_0^2/\lambda_-+M_4+1/\varepsilon_{\mathrm{ref}}+1/\psi+m$;
--   - for every point register covering $B(x_c,R_0)\cap h\mathbb Z^D$, every stage $i$ and every rational symmetric $A$ with $\lambda_-I\preceq A\preceq\lambda_+I$, there is one circuit (and one controlled circuit), each making at most $C\,(D/\psi)(1+\log\Xi)^C$ membership queries, such that for every body $K$ on a good branch $c^{-1}\mathrm{Cov}_{\pi_{b_i}}(X)\preceq A\preceq c\,\mathrm{Cov}_{\pi_{b_i}}(X)$ and every joint state $|\Psi\rangle_{SA}$ supported on the feasible labels with $\||\Psi\rangle_{SA}\|_{4,\pi_{i,\Lambda}}\le M_4$,
--   $$
--   \big\|(\tilde R\otimes I_A)(|0\rangle_E\otimes|\Psi\rangle_{SA})-|0\rangle_E\otimes(R_{\pi_{i,\Lambda}}\otimes I_A)|\Psi\rangle_{SA}\big\|\le\varepsilon_{\mathrm{ref}},
--   $$
--   and likewise for the controlled reflection.
--
--   This is the reflection oracle of every cooling stage, at $\tilde O(D/\psi)$ membership queries per call.
--
--   **Formalization Note** $\psi_D$ is `(SongZhangKLS.psiN D)⁻¹`. The circuits use arbitrary unitary gates and the membership oracle of $K$; they are chosen before $K$.
--
--   Differences from the source:
--   - reading: Õ(D/ψ) membership queries → C(D/ψ)(1 + log Ξ)^C with Ξ collecting every numeric datum of the statement; reason: the paper does not list the arguments hidden by Õ; collecting all data is the faithful reading
--   - reading: a common sufficiently fine lattice → one dyadic h = 2^{-p} with 1/h ≤ C·Ξ^C, chosen before the stage, the preconditioner and K; reason: Theorem 5.2 (p.40) bounds 1/h polynomially after rescaling the inner radius to one; Ξ contains R₀ through (1 + max‖b_i‖)R₀, so applying the statement to dyadically rescaled data gives that rescaled bound; a ∀-fine-h reading is false since the walk's radius count grows with log(1/h)
--   - reading: one circuit approximating R_{π_{i,Λ}} → a circuit over arbitrary unitary gates chosen from the data, i and A before K, seeing K only through memOracle; reason: a circuit chosen after K could implement the reflection with no query
--   - encoding: A ≍ Cov_{π_{b_i}}(X) with fixed comparison constants → ∀ c ≥ 1 ∃ C, and c⁻¹ Var ≤ uᵀAu ≤ c Var for every u; reason: two-sided Loewner comparison on quadratic forms; C may depend on the comparison constant
--   - encoding: rational preconditioner A of Theorem 5.2 (i) → symmetric rational A with λ₋‖u‖² ≤ uᵀAu ≤ λ₊‖u‖²; reason: the Loewner bounds λ₋I ⪯ A ⪯ λ₊I
--   - encoding: ψ ≤ ψ_D → ENNReal.ofReal ψ ≤ (SongZhangKLS.psiN D)⁻¹; reason: as in the main theorem
--   - encoding: the sample register → a point register of format (b, p) representing every lattice point of B(x_c, R₀) (RegCovers); reason: the register encodes a box of lattice points (p.27)
--   - reading: B(x₀, r) ⊆ K ⊆ B(x₀, R) with B(x, r) not specified open or closed → open inner ball, closed outer ball; reason: the stronger of the readings: an open inner ball and a closed outer ball admit the most bodies
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Corollary 5.3, p.40 (setting §5.1, p.37, (36); Theorem 5.2, p.40)

import Definitions.Def_QVolKLS_logAffineZ
import Definitions.Def_QVolKLS_fourthMomentNorm
import Definitions.Def_SongZhangKLS_cheegerPsi

set_option autoImplicit false

namespace QVolKLS

open QAlgorithms
open scoped ENNReal

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Corollary 5.3 (Lattice qsample
reflections)**, p.40, in the setting of §5.1 (p.37) and Theorem 5.2 (p.40): a convex body
`K ⊂ ℝ^D` with rational data `x_c, r₀, R₀`, `B(x_c, r₀) ⊆ K ⊆ B(x_c, R₀)`, rational tilts
`b_0, …, b_m`, rational `0 < λ_− ≤ λ_+`, a rational `0 < ψ ≤ ψ_D`; `π_{b_i}` is the continuous
log-affine law and `π_{i,Λ}` its lattice law on `K ∩ hℤ^D` (36).

For every comparison constant `c ≥ 1` there is `C` such that for all such data and every `M₄ ≥ 1`,
`0 < ε_ref < 1/2`: there is a common dyadic lattice spacing `h = 2^{-p}` with `1/h ≤ C Ξ^C` such that,
on a point register of format `(b, p)` representing the lattice points of `B(x_c, R₀)`, for every
stage `i` and every rational preconditioner `A` with `λ_− I ⪯ A ⪯ λ_+ I` there is one circuit (and one
controlled circuit) with at most `C (D/ψ)(1 + log Ξ)^C` membership queries per call, such that for
every body `K` on which `A ≍ Cov_{π_{b_i}}(X)` (`c^{−1}Σ_i ⪯ A ⪯ cΣ_i`) the circuit approximates
`R_{π_{i,Λ}}` to error `ε_ref` in the sense of (16) on every joint state supported on the feasible
labels with `‖|Ψ⟩_SA‖_{4,π_{i,Λ}} ≤ M₄` (and the controlled circuit approximates the controlled
reflection likewise).

**Formalization Note.**
* `ψ_D` is `(SongZhangKLS.psiN D)⁻¹` in `ℝ≥0∞` (see the main theorem).
* `Õ(D/ψ)` is `C (D/ψ)(1 + log Ξ)^C` with
  `Ξ = D + R₀/r₀ + (1 + max_i ‖b_i‖)R₀ + λ_+/λ_− + R₀²/λ_− + M₄ + 1/ε_ref + 1/ψ + m`, every numeric
  datum of the statement; "a common sufficiently fine lattice" is the existence of one dyadic `h`
  with `1/h ≤ C Ξ^C` (the paper: "1/h is at most polynomial" in these data), chosen before the
  stage, the preconditioner and the body.
* The circuits use arbitrary unitary gates and the membership oracle `memOracle K b p` (format of the
  point register); they are chosen from the data, `i` and `A`, before `K`, which they see only through
  the oracle. Workspace `E` is the first `a` wires and is returned to `|0⟩` up to the error; `A` (the
  auxiliary space `H`) is untouched.
* "On a good branch" is the hypothesis `c^{−1}Σ_i ⪯ A ⪯ cΣ_i` with `Σ_i = Cov_{π_{b_i}}(X)`, stated on
  quadratic forms (`dirVariance`, `quadForm`); `A` is symmetric with `λ_−‖u‖² ≤ uᵀAu ≤ λ_+‖u‖²`.
* `π_{i,Λ}` on the register is `regWeight`: zero off `K`, so `qsampleRefl` is `R_{π_{i,Λ}}` on the
  feasible labels and `−I` on the others; joint states are supported on the feasible labels
  (`decodePoint z ∈ K`). The controlled reflection has its control on wire `0` of the last
  `D·b + 1` wires, counted among the auxiliary registers in the fourth-moment norm. -/
theorem corollary_5_3 :
    ∀ c : ℝ, 1 ≤ c → ∃ C : ℝ, 0 < C ∧
      ∀ (D m : ℕ), 1 ≤ D → ∀ (xc : Fin D → ℚ) (r0 R0 : ℚ) (bt : Fin (m + 1) → Fin D → ℚ)
        (lm lp ψ M4 εr : ℚ), 0 < r0 → r0 ≤ R0 → 0 < lm → lm ≤ lp → 0 < ψ →
        ENNReal.ofReal (ψ : ℝ) ≤ (SongZhangKLS.psiN D)⁻¹ → 1 ≤ M4 → 0 < εr → εr < 1 / 2 →
        let Ξ : ℝ := (D : ℝ) + (R0 : ℝ) / (r0 : ℝ) + (1 + ⨆ i, ‖ratPoint (bt i)‖) * (R0 : ℝ) +
          (lp : ℝ) / (lm : ℝ) + (R0 : ℝ) ^ 2 / (lm : ℝ) + (M4 : ℝ) + 1 / (εr : ℝ) + 1 / (ψ : ℝ) +
          (m : ℝ)
        ∃ p : ℕ, (2 : ℝ) ^ p ≤ C * Ξ ^ C ∧
          ∀ b : ℕ, RegCovers D b p (Metric.closedBall (ratPoint xc) (R0 : ℝ)) →
          ∀ (i : Fin (m + 1)) (A : Matrix (Fin D) (Fin D) ℚ), A.transpose = A →
            (∀ u : Euc D, (lm : ℝ) * ‖u‖ ^ 2 ≤ quadForm A u ∧ quadForm A u ≤ (lp : ℝ) * ‖u‖ ^ 2) →
            ∃ (a : ℕ) (cp : OracleCircuit unitaryGateSet (fun _ : Fin 1 => D * b + 1) (a + D * b))
              (cc : OracleCircuit unitaryGateSet (fun _ : Fin 1 => D * b + 1)
                (a + (D * b + 1))),
              (cp.queryCount 0 : ℝ) ≤ C * ((D : ℝ) / (ψ : ℝ)) * (1 + Real.log Ξ) ^ C ∧
              (cc.queryCount 0 : ℝ) ≤ C * ((D : ℝ) / (ψ : ℝ)) * (1 + Real.log Ξ) ^ C ∧
              ∀ K : Set (Euc D), IsConvexBody K → Metric.ball (ratPoint xc) (r0 : ℝ) ⊆ K →
                K ⊆ Metric.closedBall (ratPoint xc) (R0 : ℝ) →
                (∀ u : Euc D,
                  c⁻¹ * dirVariance (logAffineMeasure K (ratPoint (bt i))) u ≤ quadForm A u ∧
                    quadForm A u ≤ c * dirVariance (logAffineMeasure K (ratPoint (bt i))) u) →
                (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                  (Ψ : Qubits (D * b) → H),
                  jointNorm Ψ = 1 → (∀ z, decodePoint D b p z ∉ K → Ψ z = 0) →
                  fourthMomentNorm (regWeight D b p K
                    (latticeLaw K ((2 : ℝ)⁻¹ ^ p) (ratPoint (bt i)))) Ψ ≤ ENNReal.ofReal M4 →
                  jointNorm (opApply (cp.unitary (fun _ => memOracle K b p)) (withZeroAnc a Ψ) -
                    withZeroAnc a (opApply (qsampleRefl (regWeight D b p K
                      (latticeLaw K ((2 : ℝ)⁻¹ ^ p) (ratPoint (bt i))))) Ψ)) ≤ εr) ∧
                (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                  (Φ : Qubits (D * b + 1) → H),
                  jointNorm Φ = 1 →
                  (∀ (cb : Bool) (z : Qubits (D * b)), decodePoint D b p z ∉ K →
                    Φ (Fin.cons cb z) = 0) →
                  fourthMomentNorm (regWeight D b p K
                    (latticeLaw K ((2 : ℝ)⁻¹ ^ p) (ratPoint (bt i)))) (ctrlAux Φ) ≤
                    ENNReal.ofReal M4 →
                  jointNorm (opApply (cc.unitary (fun _ => memOracle K b p)) (withZeroAnc a Φ) -
                    withZeroAnc a (opApply (controlledQubits (qsampleRefl (regWeight D b p K
                      (latticeLaw K ((2 : ℝ)⁻¹ ^ p) (ratPoint (bt i)))))) Φ)) ≤ εr) := by sorry

end QVolKLS
