-- Prove2me | Theorems.Thm_PrettyGoodCriterion_lemma_9
-- name    : PrettyGoodCriterion.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:37:33.443812+00:00
-- url     : https://prove2.me/theorems/c0e64253-d870-479f-9687-8c6f03c8bf78
-- title:
--   Lemma 9 — the blockwise PGM of a code is simultaneously the bitwise PGM
-- statement:
--   Let $\sigma_0,\sigma_1$ be density matrices, $\mathcal C\subseteq\{0,1\}^n$ a code with $|\mathcal C|\ge2$, $c$ a uniformly random codeword, and $\hat c\in\mathcal C$ the outcome of the PGM of $\mathcal C$ (observables $M_{\hat c}$) applied to $\sigma_c$. Fix a coordinate $i$ and put
--   $$\pi_i(b):=\Pr[c_i=b],\qquad \sigma_i(b):=\mathbb E[\sigma_c\mid c_i=b]\qquad(b\in\{0,1\}),$$
--   and $\mathcal E_i:=\{(\pi_i(0),\sigma_i(0)),(\pi_i(1),\sigma_i(1))\}$ with PGM $\{N_{\hat b}\}$. Then:
--
--   1. $\hat c_i$ is the outcome of the PGM of $\mathcal E_i$: $N_{\hat b}=\sum_{\hat c:\,\hat c_i=\hat b}M_{\hat c}$ for $\hat b\in\{0,1\}$;
--   2. $\Pr[c_i=b,\ \hat c_i=\hat b]=\pi_i(b)\operatorname{Tr}(\sigma_i(b)N_{\hat b})$ for all $b,\hat b$;
--   3. consequently
--   $$\Pr[\hat c_i\neq c_i]=p_e(\mathcal E_i).$$
--
--   This is Lemma 8 for the projection $c\mapsto c_i$; it reduces the bit error of the block PGM to a binary PGM error, which the proof of Theorem 17 then bounds by $p_e(\sigma_0,\sigma_1)$.
--
--   **Formalization Note** $\pi_i,\sigma_i$ are the pushforward prior and states of the code ensemble under $c\mapsto c_i$; $\sigma_i(b)=0$ if no codeword has $c_i=b$. Output symmetry is not assumed.
--
--   Differences from the source:
--   - encoding: σ_i(b) = E[σ_c | c_i = b], undefined when no codeword has c_i = b → σ_i(b) = 0 in that case; reason: then π_i(b) = 0, and the label contributes to no PGM operator and no error term
--   - reading: ĉ_i is the outcome of the PGM of ℰ_i when applied to σ_i(c_i) → the operator identity N_b̂ = ∑_{ĉ_i = b̂} M_ĉ together with the joint law of (c_i, ĉ_i); reason: the stronger reading, as for Lemma 8, of which this is the specialization
--   - encoding: the PGM of 𝒞, i.e. of the uniform ensemble {(|𝒞|⁻¹, σ_c) : c ∈ 𝒞} with outcomes ĉ ∈ 𝒞 → the PGM (Definition 2.7) of the ensemble indexed by the subtype {c // c ∈ 𝒞} with prior |𝒞|⁻¹ and states HolevoCQ.wordState σ n c; reason: the same ensemble; the outcome set is the code itself
--   - encoding: ℂ^d, d × d matrices → matrices indexed by an arbitrary finite type ι; reason: ℂ^d is the case ι = Fin d, and every finite type is Fin d up to relabelling, which changes no trace, product or positivity
--   - encoding: probabilities Tr(σ_x M_x̂) (and the other traces of products of positive semidefinite matrices) → real parts of the traces; reason: these traces are real; taking the real part changes no value
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Lemma 9, p.18 (PDF 20)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PrettyGoodCriterion_pgmError
import Definitions.Def_PrettyGoodCriterion_pushState
import Definitions.Def_PrettyGoodCriterion_codePGM

open scoped ComplexOrder

namespace PrettyGoodCriterion

/-- **Lemma 9 (Blockwise PGM is simultaneously bitwise PGM)**, Alrabiah–Guruswami,
arXiv:2608.09347 (held version), p.18 (PDF 20); the specialization of Lemma 8 to
`f_i(c) = c_i`.

For a binary-input cq channel with density outputs `σ₀, σ₁`, a code `𝒞 ⊆ {0,1}ⁿ` (`|𝒞| ⩾ 2`, the
standing assumption of p.14) and a coordinate `i`, let `ĉ` be the outcome of the PGM of the
uniform code ensemble applied to `σ_c`, `π_i(b) := Pr[c_i = b]` and `σ_i(b) := E[σ_c | c_i = b]`.
Then

1. `ĉ_i` is the outcome of the PGM of `ℰ_i = {(π_i(0), σ_i(0)), (π_i(1), σ_i(1))}`: its
   observables are `N_b̂ = ∑_{ĉ : ĉ_i = b̂} M_ĉ`;
2. the joint law: `Pr[c_i = b, ĉ_i = b̂] = π_i(b) Tr(σ_i(b) N_b̂)`;
3. `Pr[ĉ_i ≠ c_i] = p_e(ℰ_i)`.

**Formalization Note.** `π_i` and `σ_i` are the pushforward prior and state of the code ensemble
under `c ↦ c_i` (`pushPrior`, `pushState`); `σ_i(b) = 0` if no codeword has `c_i = b`. Output
symmetry is not assumed (the lemma does not need it). -/
theorem lemma_9 {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Fin 2 → Matrix ι ι ℂ)
    (hσ : ∀ b, QAlgorithms.IsDensityMatrix (σ b)) {n : ℕ} (C : Finset (Fin n → Fin 2)) (hC : 2 ≤ C.card)
    (i : Fin n) :
    (∀ bh : Fin 2,
        pgm (pushPrior (codePrior C) (fun c : C => c.1 i))
            (pushState (codePrior C) (codeStates σ C) (fun c : C => c.1 i)) bh =
          ∑ ch ∈ Finset.univ.filter (fun ch : C => ch.1 i = bh), codePGM σ C ch) ∧
    (∀ b bh : Fin 2,
        ∑ c ∈ Finset.univ.filter (fun c : C => c.1 i = b),
          ∑ ch ∈ Finset.univ.filter (fun ch : C => ch.1 i = bh),
            codePrior C c * (codeStates σ C c * codePGM σ C ch).trace.re =
          pushPrior (codePrior C) (fun c : C => c.1 i) b *
            (pushState (codePrior C) (codeStates σ C) (fun c : C => c.1 i) b *
              pgm (pushPrior (codePrior C) (fun c : C => c.1 i))
                (pushState (codePrior C) (codeStates σ C) (fun c : C => c.1 i)) bh).trace.re) ∧
    (∑ c : C, ∑ ch ∈ Finset.univ.filter (fun ch : C => ch.1 i ≠ c.1 i),
        codePrior C c * (codeStates σ C c * codePGM σ C ch).trace.re =
      pgmError (pushPrior (codePrior C) (fun c : C => c.1 i))
        (pushState (codePrior C) (codeStates σ C) (fun c : C => c.1 i))) := by sorry

end PrettyGoodCriterion
