-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_generalized_adversary_bound
-- name    : QAlgorithms.DeWolf.generalized_adversary_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:42:44.756178+00:00
-- url     : https://prove2.me/theorems/cc74b25a-5969-43e3-9bc7-7ce4b0a95678
-- title:
--   Generalized (negative-weights) adversary lower bound
-- statement:
--   This is the generalized adversary bound of Høyer, Lee and Špalek.
--
--   Let $f : D \to \{0,1\}$ with $D \subseteq \{0,1\}^N$, and let $\Gamma$ be an adversary matrix for $f$: a real symmetric $|D| \times |D|$ matrix with $\Gamma_{xy} = 0$ whenever $f(x) = f(y)$. For $i \in [N]$ let $\Gamma_i$ be $\Gamma$ with the entries $\Gamma_{xy}$ for which $x_i = y_i$ set to $0$, and let $\|\cdot\|$ denote the operator norm. Let $0 \le \varepsilon < 1/2$. If a $T$-query quantum algorithm $U_T O_x U_{T-1} \cdots U_1 O_x U_0$ (input-independent unitaries, any workspace, standard query $O_x : |i,b\rangle \mapsto |i,b\oplus x_i\rangle$, followed by a measurement) outputs $f(x)$ with probability at least $1 - \varepsilon$ for every $x \in D$, then
--
--   $$
--   T \ge \left(\frac12 - \sqrt{\varepsilon(1-\varepsilon)}\right) \frac{\|\Gamma\|}{\max_{i \in [N]} \|\Gamma_i\|}.
--   $$
--
--   Optimizing over $\Gamma$ gives the quantity $\mathrm{ADV}^{\pm}(f)$, which is a lower bound on bounded-error quantum query complexity.
--
--   **Formalization Note** If $\max_i \|\Gamma_i\| = 0$ then $\Gamma = 0$ (every nonzero entry has $x \ne y$ and so survives in some $\Gamma_i$), and Lean's convention $a/0 = 0$ makes the bound $T \ge 0$, matching the source's vacuous bound.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 112, §12.1, Theorem 2. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Adversary
set_option autoImplicit false

namespace QAlgorithms.DeWolf



/-- de Wolf §12.1, Theorem 2 (generalized adversary bound, Høyer–Lee–Špalek; PDF p. 112): let
`f : D → {0,1}` with `D ⊆ {0,1}^N` and let `Γ` be an adversary matrix for `f`. Every `T`-query
algorithm (any workspace, any output rule) that computes `f` with worst-case error probability at
most `ε < 1/2` satisfies `T ≥ (1/2 − √(ε(1−ε))) ‖Γ‖ / max_{i ∈ [N]} ‖Γ_i‖`. When
`max_i ‖Γ_i‖ = 0` the matrix `Γ` is zero and the bound reads `T ≥ 0` (Lean's `x / 0 = 0`). -/
theorem generalized_adversary_bound {N : ℕ} (f : (Fin N → Bool) → Bool)
    (D : Finset (Fin N → Bool)) (Γ : Matrix D D ℝ) (hΓ : IsAdversaryMatrix f D Γ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin N) Bool W T) (out : (Fin N × Bool) × W → Bool)
    (hA : A.ComputesWithError out D f ε) :
    (1 / 2 - Real.sqrt (ε * (1 - ε))) * specNorm Γ / maxMaskedNorm Γ ≤ (T : ℝ) := by
  sorry




end QAlgorithms.DeWolf
