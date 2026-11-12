-- Prove2me | Theorems.Thm_TorchFire_TF_lemma_7_6
-- name    : TorchFire.TF.lemma_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:47:10.055674+00:00
-- url     : https://prove2.me/theorems/a0a00d52-64a4-4811-b363-12280098a98a
-- title:
--   Lemma 7.6 — $\Vert(R^O_{c,e}-U_{\mathrm{affine}_{a_c,e}})|\psi\rangle\Vert\le2\sqrt d$ (54) and $\mathbb E[d]\le2L(R+1)e(\lambda)+\mathbb E[e_{\mathrm{tag}}]\le\mathrm{negl}$ (55)
-- statement:
--   Fix an honest serial $s=(\ell,a)$ and $t\in T_{\mathrm{pub}}$, and set $d=\min\{1,e_A+e_T+e_{\mathrm{tag}}\}$ (53), with $e_A,e_T$ the anchor and torch signing errors (50) and $e_{\mathrm{tag}}$ the coherent tag error (51). For any normalized $|\phi\rangle_{XCE}$ let
--   $$|\psi\rangle=|A_a\rangle|T_t\rangle|K\rangle\otimes|\phi\rangle_{XCE}\otimes|0\rangle_W,$$
--   where $X,C$ are the affine-input and answer registers and $E,W$ are auxiliary workspace registers. Then for every $c\in[L]$ and $e\in\{0,1\}$,
--   $$\big\Vert(R^O_{c,e}-U_{\mathrm{affine}_{a_c,e}})|\psi\rangle\big\Vert\le2\sqrt d\quad(54),$$
--   where the ideal query acts only on $X,C$. Moreover
--   $$\mathbb E[d]\le2L(R+1)e(\lambda)+\mathbb E[e_{\mathrm{tag}}]\le\mathrm{negl}(\lambda)\quad(55)$$
--   for polynomially bounded $R$, with $e(\lambda)=2^{-\lambda}+2^{-24\lambda}$.
--
--   The lemma says that the coherent affine query through $\Gamma$, built from the anchor, the torch and the CGS flame, behaves like the private affine oracle and returns its resources nearly intact; it carries the cloning correctness of torch-fire.
--
--   Differences from the source:
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - encoding: negl(λ) and polynomials → ν ≥ 0 with ν(λ) ≤ λ^{−c} eventually for every c > 0; p(λ) ≤ (λ+2)^c (published PPADSIS.SubexpSIS definitions); reason: paper.md decision 8; equivalent to p.16 for nonnegative ν
--   - encoding: OSS.Sign with intermediate measurements; U^O_{y,b} obtained from it by Fact 3.1 (Remark 4.12) → the deferred-measurement signing circuit written gate by gate; the zero state of Σ is |⊥⟩; reason: paper.md decisions 6 and 16
--   - encoding: Dig : {0,1}* → {0,1}^L (14) → Dig uniform on {0,1}^{≤ 1+λ+2Lr}; reason: paper.md decision 10; every message signed in torch-fire has length 1+λ+2Lr
--   - reading: TF.GenOracles(1^λ) (Definition 6.1) → TF.GenOracles(1^λ, 1^R) (Construction 7.4 item 1); reason: paper.md decision 11: the oracle T publishes the R torch keys
--   - encoding: e_tag: sup over unit vectors of Z ⊗ E → sup over unit vectors of Z alone; reason: the supremum of ⟨ψ|(M_Z ⊗ I_E)|ψ⟩ does not depend on E
--   - reading: E[d], "expectations are over the sampling of the oracles and classical keys" (p.54) → average over the oracle sample (with the torch keys) and a uniform serial (ℓ, a); reason: the honest serial is uniform by Construction 4.6
--   - encoding: the affine-input and answer registers X, C → one register pair (X of n − r qubits, Y of k qubits, two ⊥ flags) for both e; for e = 0 the input is X and the answer Y, for e = 1 the reverse; reason: one type for both e; the ideal query touches only X, C
--   - encoding: S^O_{c,e} copies q into a register Q read by Γ → Γ reads s, t, c, e as parameters and u from the affine registers; reason: the same operator R^O_{c,e}
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Lemma 7.6, (53)–(55), p.55; (50)–(51) p.54; proof in App. C.2, p.84

import Mathlib
import Definitions.Def_TorchFire_TF_cloneTF
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS PPADSIS.SubexpSIS

namespace TorchFire.TF

/-- **Lemma 7.6**, (53)–(55), p.55 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593; proof in App. C.2). Fix an honest serial `s = (ℓ, a)` and
`t ∈ T_pub`, and set `d = min{1, e_A + e_T + e_tag}` (53). For every finite register `E`, every
normalized `|ϕ⟩_{XCE}` (`X, C` the affine-input and answer registers), and
`|ψ⟩ = |A_a⟩|T_t⟩|K⟩ ⊗ |ϕ⟩_{XCE} ⊗ |0⟩_W` (`W` the auxiliary registers), for every `c ∈ [L]` and
`e ∈ {0, 1}`: `‖(R^O_{c,e} − U_{affine_{a_c,e}})|ψ⟩‖ ≤ 2√d` (54), where the ideal query acts only on
`X, C`. Moreover `E[d] ≤ 2L(R + 1)e(λ) + E[e_tag] ≤ negl(λ)` (55), the expectation over the oracles, the
torch keys and the honest serial. -/
theorem lemma_7_6 :
    (∀ (lam R : ℕ) (ω : Sample lam R) (s : Serial lam) (t : Key lam), InTpub ω t →
      ∀ (E : Type) [Fintype E] [DecidableEq E] (ϕ : AffPair lam × E → ℂ), l2norm ϕ = 1 →
      ∀ (c : Fin (L lam)) (e : ZMod 2),
        l2norm ((liftOn (fun x : RSpace lam × E => (x.1, x.2)) (Rce ω s t c e) -
            liftOn (fun x : RSpace lam × E => (x.1.2.1, (x.1.1, x.1.2.2, x.2))) (Uaff ω s c e)).mulVec
          (fun x : RSpace lam × E =>
            if x.1.2.2 = rws0 then
              longKeyState (OA ω s.1) s.2 x.1.1.1 * longKeyState (OT ω) t x.1.1.2.1 *
                CGS.flameVec (OK ω) x.1.1.2.2 * ϕ (x.1.2.1, x.2)
            else 0)) ≤ 2 * Real.sqrt (dErr ω s)) ∧
    (∀ lam R : ℕ, 2 ≤ lam →
      avg (Sample lam R × Serial lam) (fun p => dErr p.1 p.2) ≤
        2 * L lam * (R + 1) * eLam lam + avg (Sample lam R) etag) ∧
    ∀ R : ℕ → ℕ, PolyBounded R →
      Negligible fun lam => avg (Sample lam (R lam) × Serial lam) (fun p => dErr p.1 p.2) := by sorry

end TorchFire.TF
