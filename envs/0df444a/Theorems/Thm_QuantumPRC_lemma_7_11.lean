-- Prove2me | Theorems.Thm_QuantumPRC_lemma_7_11
-- name    : QuantumPRC.lemma_7_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:23.104546+00:00
-- url     : https://prove2.me/theorems/a7a68a74-3a3e-4b60-a24e-2f1d4db931ee
-- title:
--   Lemma 7.11 — pseudorandomness of Construction 7.2
-- statement:
--   Let $n_{\mathrm L},\ell,r,m$ be efficient polynomial lengths and $n_{\mathrm P}=n_{\mathrm L}+\ell+r+m$, with $n_{\mathrm P}(\lambda)\ge\lambda^\kappa$ for some $\kappa>0$, $r(\lambda)\ge n_{\mathrm L}(\lambda)+\ell(\lambda)+\omega(\log\lambda)$ and $\ell(\lambda)=\omega(\log\lambda)$. Consider Construction 7.2 with an efficient, pseudorandom $(n_{\mathrm L}+\ell,m)$ PRFC, a PRF $F:\{0,1\}^\lambda\times\{0,1\}^{n_{\mathrm L}+\ell}\to\{0,1\}$ giving $f_k$, a PRP $\Pi$ on $\{0,1\}^{n_{\mathrm L}+\ell+r}$ giving $\pi_{k'}$, and any PPT graph sampler. Then for every parameter sequence $W\le n_{\mathrm P}$ and every uniform QPT adversary $\mathcal A$,
--
--   $$
--   \Big|\Pr_{\mathsf{sk}\leftarrow\mathsf{KeyGen}(1^\lambda,1^{W(\lambda)})}\big[1\leftarrow\mathcal A^{\mathrm{Enc}_{\mathsf{sk}}}\big]-\Pr_{V\leftarrow\mu_{n_{\mathrm L}\to n_{\mathrm P}}}\big[1\leftarrow\mathcal A^{V}\big]\Big|\le\mathsf{negl}(\lambda).
--   $$
--
--   Differences from the source:
--   - generalization: Construction 7.2 with a PRFC robust to any p-bounded channel and GraphSample of Theorem 7.1 (instantiated with p_g and t), nP even for large λ → any efficient and pseudorandom PRFC, any PPT graph sampler, any parity of nP, and any scheme parameter W ≤ nP; reason: the pseudorandomness proof uses neither robustness nor the graph properties nor parity; the printed construction is a special case
--   - reading: QPT algorithm / QPT adversary (no machine model given) → uniform families of Clifford+T oracle circuits printed by a polynomial-time Turing machine; PPT algorithms are polynomial-time functions of polynomially many fair coins; reason: the paper fixes no model; this one covers adaptive and reference-entangled queries and is used on both sides of every implication (paper.md decision 3)
--   - generalization: nL, ℓ, r, m are polynomials (p.40) → they are EffPoly lengths: polynomially bounded and computable from 1^λ in polynomial time; reason: every integer-valued polynomial is such a length, so the Lean statement contains the printed one (paper.md decision 2)
--   - encoding: the Haar measure µ_{nL→nP} on isometries → V = U·ι with U Haar on U(2^{nP}) (QAlgorithms.Schur.unitaryHaar) and ι|x⟩ = |x⟩|0^{nP−nL}⟩; reason: the realization used on p.69 of the paper; same law
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Lemma 7.11, p.50 (proof pp.50–51); Construction 7.2, p.41

import Mathlib
import Definitions.Def_QuantumPRC_C72

open Filter Asymptotics

namespace QuantumPRC

open Classical in
/-- **Lemma 7.11** (pseudorandomness of Construction 7.2). Hsieh, Yamada, arXiv:2609.38986 (sha256
6901b59d…), Lemma 7.11, p.50: "If `nP(λ) ≥ λ^κ` for some constant `κ > 0`, `r(λ) ≥ nL(λ) + ℓ(λ) + ω(log λ)`,
and `ℓ(λ) ≥ ω(log λ)`, then Construction 7.2 satisfies pseudorandomness."

Construction 7.2, p.41, uses an `(nL + ℓ, m)` PRFC, a PRF `F : {0,1}^λ × {0,1}^{nL+ℓ} → {0,1}`, a PRP `Π` on
`{0,1}^{nL+ℓ+r}` and GraphSample (PPT); `nL, ℓ, r, m` are polynomials. Here the PRFC is required to be
efficient and pseudorandom (Definition 6.1), GraphSample is any PPT sampler, and the parameter `W`
passed to the scheme is any sequence with `W ≤ nP`.

**Formalization Note.** `f_k(z) = F(k, z)` (one output bit) and `π_{k′} = Π(k′, ·)`. The conclusion is
`ChScheme.Pseudorandom` (44) against the Haar isometry. -/
theorem lemma_7_11 (D : C72) (F : PRF (fun lam => D.nL lam + D.ℓ lam) (fun _ => 1))
    (Pm : PRP (fun lam => D.nL lam + D.ℓ lam + D.r lam))
    (hnL : EffPoly D.nL) (hℓ : EffPoly D.ℓ) (hr : EffPoly D.r) (hm : EffPoly D.m)
    (hf : ∀ lam k x, D.f lam k x = F.F lam k x 0)
    (hπ : ∀ lam k, ⇑(D.perm lam k) = Pm.P lam k)
    (hprfc : D.prfc.Efficient ∧ D.prfc.Pseudorandom) (hF : F.IsPRF) (hP : Pm.IsPRP)
    (hgs : PolyBounded D.gc ∧ ∃ GSm : List Bool → List Bool, CookPvsNP.PolyTimeComputable GSm ∧
      ∀ T n ρ, GSm (tupleCode [unary n, unary T, bits ρ]) = adjCode (D.gs T n ρ))
    (hκ : ∃ κ : ℝ, 0 < κ ∧ ∀ lam : ℕ, (lam : ℝ) ^ κ ≤ D.nP lam)
    (hrω : SuperLog fun lam => (D.r lam : ℝ) - D.nL lam - D.ℓ lam)
    (hℓω : SuperLog fun lam => (D.ℓ lam : ℝ))
    (W : ℕ → ℕ) (hW : ∀ lam, W lam ≤ D.nP lam) :
    D.scheme.Pseudorandom W := by sorry

end QuantumPRC
