-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P39_finiteHolevoOptimization
-- name    : QAlgorithms.Papers.Independent.Support50.P39.finiteHolevoOptimization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:59:44.464988+00:00
-- url     : https://prove2.me/theorems/c3ca58e9-9eb1-4fa8-9354-d0b209395d35
-- title:
--   Finite Holevo optimization and attaining unitary encoding
-- statement:
--   Let $\rho_{AB}$ be a normalized finite dimensional density operator, with both local dimensions positive and not necessarily equal. Fix $n\ge1$ resource copies and an output dimension $d\ge1$. All entropies are in bits. Define $H_d(\rho^{\otimes n})$ to be the supremum of the Holevo score
--
--   $$
--   \chi(\{p_i,\sigma_i\})=S\!\left(\sum_i p_i\sigma_i\right)-\sum_i p_iS(\sigma_i),
--   \qquad \sigma_i=(\Lambda_i\otimes\mathrm{id})(\rho^{\otimes n}),
--   $$
--
--   over every finite probability distribution $(p_i)$ and CPTP maps $\Lambda_i:A^{\otimes n}\to\mathbb C^d$. Then, with $I^B(\sigma)=\max\{S(\sigma_B)-S(\sigma),0\}$,
--
--   $$
--   H_d(\rho^{\otimes n})=\log_2d+sup_{\Lambda:A^{\otimes n}\to\mathbb C^d}
--   I^B\bigl((\Lambda\otimes\mathrm{id})(\rho^{\otimes n})\bigr).
--   $$
--
--   An optimal channel $\Lambda_*$ exists, together with $d^2$ unitaries $U_i$ such that $\sum_iU_iMU_i^\dagger=0$ for every traceless $d\times d$ matrix $M$. With probabilities $p_i=d^{-2}$, the encoders $\mathrm{Ad}(U_i)\circ\Lambda_*$ attain $H_d$. Moreover, the same unitary family works for every CPTP preprocessing $\Lambda$: its encoding ensemble is admissible and, writing $\sigma=(\Lambda\otimes\mathrm{id})(\rho^{\otimes n})$, its score is exactly
--
--   $$
--   \chi=\log_2d+S(\rho_B^{\otimes n})-S(\sigma).
--   $$
--
--   The last identity uses the signed entropy difference, even if negative. Only the optimized expression can use clipped coherent information. The statement includes $d=1$, when the optimized value is zero and the unitary family has one member.
--
--   This is the finite optimization identity proved on pp.4–5. It supplies an explicit attaining ensemble without equating the objective to the unrestricted fixed-$(d,n)$ operational capacity.
-- source:
--   Classical capacity of a noiseless quantum channel assisted by noisy entanglement, arXiv:quant-ph/0106080v3, PDF p. 4, RHS of Eq. (9) and Eqs. (10)–(13)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P39

namespace QAlgorithms.Papers.Independent.Support50.P39

noncomputable section

open QAlgorithms

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:quant-ph/0106080v3, PDF pp.4--6, Eqs. (9)--(13): the finite
Holevo objective H_d equals log2 d plus optimized clipped coherent information,
and an optimal CPTP map and d^2-element unitary encoding attain it.
The SAME twirling family gives, for EVERY preprocessing map, the signed
per-map identity chi=log2 d+S(B^n)-S(sigma). Clipping is used only at the
optimized value. This includes d=1 (both sides zero) and does not identify
H_d with the unrestricted fixed-(d,n) operational capacity. -/
theorem finiteHolevoOptimization {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    denseCodingHolevoValue rho n d = Real.logb 2 d + finiteCoherentOpt rho n d ∧
    ∃ Phi : Superop (Fin n → A) (Fin d), IsChannel Phi ∧
      clippedCoherentInformation (aliceAction Phi (noisyResourceCopies rho n)) =
        finiteCoherentOpt rho n d ∧
      ∃ U : Fin (d*d) → Matrix.unitaryGroup (Fin d) ℂ,
        TracelessTwirling U ∧
        (∀ Psi : Superop (Fin n → A) (Fin d), IsChannel Psi →
          IsEncoding (uniformWeight d) (unitaryEncoders Psi U) ∧
          encodingHolevo rho n (uniformWeight d) (unitaryEncoders Psi U) =
            Real.logb 2 d + vnEntropy (traceLeft (noisyResourceCopies rho n)) -
              vnEntropy (aliceAction Psi (noisyResourceCopies rho n))) ∧
        encodingHolevo rho n (uniformWeight d) (unitaryEncoders Phi U) =
          denseCodingHolevoValue rho n d := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P39
