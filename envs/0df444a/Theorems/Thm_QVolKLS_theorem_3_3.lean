-- Prove2me | Theorems.Thm_QVolKLS_theorem_3_3
-- name    : QVolKLS.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:40:21.319447+00:00
-- url     : https://prove2.me/theorems/94615b95-dcb2-4dc4-b308-847c0599ec59
-- title:
--   Theorem 3.3 — input-dependent stationary-state reflection with $O(\sqrt t\log(1/\zeta))$ block-encoding queries
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let the sample register have $s$ qubits, let $b\in\mathbb N$, $t\ge1$ and $0<\eta,\zeta<\tfrac12$. There is a unitary circuit $\tilde R$ on $S$ and a fresh register $E$ of $a\le b+C$ ancilla qubits, and a controlled version of it, each using at most $C\sqrt t\log(1/\zeta)$ queries to a block-encoding, such that the following holds.
--
--   Let $\Omega$ be a feasible set of register labels and $P$ a finite positive, ergodic, reversible chain on $\Omega$ with stationary law $\pi$ and $\tau_{\mathrm{mix},2}(\eta,\pi;P)\le t$. Given controlled access to a $(1,b,0)$-block-encoding of $D_\pi\oplus0$, for every joint state $|\Psi\rangle_{SA}$ supported on $\Omega$,
--   $$
--   \big\|(\tilde R\otimes I_A)(|0^a\rangle_E\otimes|\Psi\rangle_{SA})-|0^a\rangle_E\otimes(R_\pi\otimes I_A)|\Psi\rangle_{SA}\big\|\ \le\ C\big(\eta^{1/4}\||\Psi\rangle_{SA}\|_{4,\pi}+\zeta\big),
--   \tag{16}
--   $$
--   where $R_\pi$ acts as $R_\pi\oplus(-I_{\mathrm{bad}})$ on the whole register. The same cost and bound hold for the controlled reflection, its control included among the auxiliary registers when evaluating the fourth-moment norm.
--
--   This is the reflection used for every qsample in the volume algorithm: it needs only warm-start mixing, not a spectral gap.
--
--   **Formalization Note** Circuits use arbitrary unitary gates and one oracle, the block-encoding $U$ (plain, inverse or controlled calls); they are fixed from $s,b,t,\eta,\zeta$ before the chain and $U$. Taking $\Omega$ to be every label gives the printed theorem.
--
--   Differences from the source:
--   - generalization: a finite chain on the whole sample register (Theorem 3.3) → a chain on any feasible set Ω of register labels, with a block-encoding of D_π ⊕ 0 and target R_π ⊕ (−I_bad), on inputs supported on Ω; reason: the p.27 zero-extension paragraph; Ω = all labels is the printed theorem
--   - reading: given controlled access to a block-encoding of D_π, there is a unitary R̃ … using O(√t log(1/ζ)) block-encoding queries → one circuit chosen from s, b, t, η, ζ before Ω, P, π and U, accessing the chain only through U; reason: a circuit chosen after the chain could implement R_π with no query
--   - encoding: positive (spectrum in [0, 1]) and ergodic (ker(I − P) = span{1}) → ⟨f, Pf⟩_π ≥ 0 for real f; real fixed points of P on Ω are constant; reason: equivalent for reversible stochastic P on a finite set
--   - encoding: τ_mix,2(η, π; P) ≤ t → every start ν ≤ 2π reaches d_TV ≤ η within t steps (MixTime2Le); reason: the definition of p.23 unfolded
--   - encoding: ≲ and O(1), O(·) → one absolute constant C for the error, the ancilla count and the query count; reason: universal constants (p.21)
--   - encoding: every joint state |Ψ⟩_SA → every Ψ : {0,1}^s → H of norm 1, H any complex inner product space; reason: covers every auxiliary register
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Theorem 3.3, p.26, and the zero-extension paragraph, p.27; definitions §2.3, pp.22–23

import Definitions.Def_QVolKLS_MixTime2Le

set_option autoImplicit false

namespace QVolKLS

open QAlgorithms
open scoped ENNReal

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Theorem 3.3 (Input-dependent
stationary-state reflection)**, p.26, with the zero-extension paragraph of p.27.

There is an absolute `C > 0` such that for every sample register of `s` qubits, every `b`, every
`t ≥ 1` and every `0 < η, ζ < 1/2` there are circuits `R̃` (on `E ⊗ S`) and its controlled version,
with `a ≤ b + C` workspace qubits, each making at most `C √t log(1/ζ)` block-encoding queries, such
that: for every feasible set `Ω` of labels and every finite positive, ergodic, reversible chain `P` on
`Ω` with stationary law `π` and `τ_mix,2(η, π; P) ≤ t`, every exact `(1, b, 0)`-block-encoding `U` of
`D_π ⊕ 0`, and every joint state `|Ψ⟩_SA` supported on `Ω`,
`‖(R̃ ⊗ I_A)(|0^a⟩_E ⊗ |Ψ⟩_SA) − |0^a⟩_E ⊗ (R_π ⊗ I_A)|Ψ⟩_SA‖ ≤ C (η^{1/4} ‖|Ψ⟩_SA‖_{4,π} + ζ)`
(16), the reflection being `R_π ⊕ (−I_bad)` on the whole register; and the same bound holds for the
controlled reflection, its control counted among the auxiliary registers.

**Formalization Note.**
* The circuits use arbitrary unitary gates (`unitaryGateSet`; the theorem counts block-encoding
  queries) and one oracle, the block-encoding unitary `U` on `b + s` qubits (ancilla first), called
  plainly, inversely or under a control. They are chosen from `s, b, t, η, ζ` before `Ω`, `P`, `π` and
  `U`: the chain enters only through `U`.
* Joint states are functions `Ψ : {0,1}^s → H` into any complex inner product space `H` (the
  auxiliary registers), of norm `1`. Workspace `E` is the first `a` wires.
* `qsampleRefl π` with `π` zero off `Ω` is `R_π ⊕ (−I_bad)`. For `Ω` the whole register this is the
  printed theorem; a proper feasible set `Ω` is the p.27 extension ("We use a block-encoding of
  `D_π ⊕ 0` … approximates `R_π ⊕ (−I_bad)` … on inputs supported on the feasible space").
* The controlled reflection acts on `(control) ⊗ S`, the control being wire `0` of the last `s + 1`
  wires (`controlledQubits`); its fourth-moment norm regroups the control with `A` (`ctrlAux`).
* `≲` and `O(1)`, `O(·)` are one absolute constant `C`. The bound is in `ℝ≥0∞` (an infinite
  fourth-moment norm makes it trivially true, as on p.26). -/
theorem theorem_3_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s b t : ℕ) (η ζ : ℝ), 1 ≤ t → 0 < η → η < 1 / 2 → 0 < ζ → ζ < 1 / 2 →
        ∃ (a : ℕ) (c : OracleCircuit unitaryGateSet (fun _ : Fin 1 => b + s) (a + s))
          (cc : OracleCircuit unitaryGateSet (fun _ : Fin 1 => b + s) (a + (s + 1))),
          (a : ℝ) ≤ b + C ∧
          (c.queryCount 0 : ℝ) ≤ C * Real.sqrt t * Real.log (1 / ζ) ∧
          (cc.queryCount 0 : ℝ) ≤ C * Real.sqrt t * Real.log (1 / ζ) ∧
          ∀ (Ω : Finset (Qubits s)) (P : Qubits s → Qubits s → ℝ) (π : Qubits s → ℝ),
            IsReversibleChainOn Ω P π → IsPositiveChain Ω P π → IsErgodicChain Ω P →
            MixTime2Le Ω η π P t →
            ∀ U : Matrix (Qubits (b + s)) (Qubits (b + s)) ℂ,
              IsZeroExtBlockEncoding U (discriminantExt Ω π P) →
              (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Ψ : Qubits s → H),
                jointNorm Ψ = 1 → (∀ x, x ∉ Ω → Ψ x = 0) →
                ENNReal.ofReal (jointNorm (opApply (c.unitary (fun _ => U)) (withZeroAnc a Ψ) -
                    withZeroAnc a (opApply (qsampleRefl π) Ψ))) ≤
                  ENNReal.ofReal C *
                    (ENNReal.ofReal (η ^ (1 / 4 : ℝ)) * fourthMomentNorm π Ψ +
                      ENNReal.ofReal ζ)) ∧
              (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                (Φ : Qubits (s + 1) → H),
                jointNorm Φ = 1 → (∀ (cb : Bool) (x : Qubits s), x ∉ Ω → Φ (Fin.cons cb x) = 0) →
                ENNReal.ofReal (jointNorm (opApply (cc.unitary (fun _ => U)) (withZeroAnc a Φ) -
                    withZeroAnc a (opApply (controlledQubits (qsampleRefl π)) Φ))) ≤
                  ENNReal.ofReal C *
                    (ENNReal.ofReal (η ^ (1 / 4 : ℝ)) * fourthMomentNorm π (ctrlAux Φ) +
                      ENNReal.ofReal ζ)) := by sorry

end QVolKLS
