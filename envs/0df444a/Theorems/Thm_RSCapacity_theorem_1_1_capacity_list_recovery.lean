-- Prove2me | Theorems.Thm_RSCapacity_theorem_1_1_capacity_list_recovery
-- name    : RSCapacity.theorem_1_1_capacity_list_recovery
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:18.976112+00:00
-- url     : https://prove2.me/theorems/5fb1b841-3a1b-4ae0-ae7d-0b4c5dca9540
-- title:
--   Theorem 1.1 (Capacity decoding and field-size-independent lists)
-- statement:
--   Fix $\gamma\in(0,1)$ and an integer $L\ge1$. There are constants $C_{\mathrm{alg}}=C_{\mathrm{alg}}(\gamma,L)$, $C_{\mathrm{list}}=C_{\mathrm{list}}(\gamma,L)$ and $n_0=n_0(\gamma,L)$ such that the following holds. Let $n\ge n_0$, let $q\ge n$ be prime, let $D\subseteq\mathbb F_q$ have $n$ distinct points, and let $1\le k\le(1-\gamma)n$. For arbitrary lists with $|S_i|\le L$:
--   1. all polynomials in $\mathcal L(D,k,\mathbf S,k+\lceil\gamma n\rceil)$ can be found deterministically using at most $q^{C_{\mathrm{alg}}}$ field operations;
--   2. $\bigl|\mathcal L(D,k,\mathbf S,k+\lceil\gamma n\rceil)\bigr|\le n^{C_{\mathrm{list}}}$;
--   3. in particular, $\mathrm{RS}_{\mathbb F_q}(D,k)$ is list decodable at radius $1-k/n-\gamma$: every Hamming ball of relative radius $1-k/n-\gamma$ contains at most $n^{C_{\mathrm{list}}}$ codewords.
--
--   The list size is polynomial in $n$ and independent of $q$, and the decoder runs in polynomial time whenever $q=n^{O(1)}$. In the formal statement the decoder is one coin-free program of the algebraic RAM, chosen together with the constants after $\gamma,L$, that outputs every polynomial of the list exactly once within $q^{C_{\mathrm{alg}}}$ steps.
--
--   Differences from the source:
--   - reading: can be found deterministically using at most q^{C_alg} field operations (machine not stated) → the published algebraic RAM over ZMod q (MatroidSensOracle.aexec), one coin-free program, steps counting every instruction, halting within the bound for every word length w with bound < 2^w; program and constants chosen after γ, L; reason: field operations are at most the step count; the strongest uniform reading
--   - reading: all polynomials in ℒ can be found → the output list has no repetitions and its members are exactly ℒ; reason: the strongest reading of finding all of ℒ
--   - encoding: arbitrary lists |S_i| ≤ L → duplicate-free lists of length ≤ L in any order, S_i their sets; words [n, k, A, |S_1|, …, |S_n|] with A = k + ⌈γn⌉, field cells [α_1, …, α_n] ++ S_1 ++ ⋯ ++ S_n; reason: input layout; every order is accepted and empty lists are allowed
--   - encoding: |ℒ| ≤ n^{C_list} and the list-decodability size → Set.encard; reason: finiteness is part of the claim
--   - reading: effective constants; deterministic polynomial time whenever q = n^{O(1)} → constants existential with the stated dependence; the polynomial-time sentence is not a separate clause; reason: effectiveness describes the proof; q ≤ n^c gives q^{C_alg} ≤ n^{c·C_alg} from clause (a)
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Theorem 1.1, pp.1–2 (PDF 3–4); proof on pp.30–31 (PDF 32–33)

import Mathlib
import Definitions.Def_MatroidSensOracle_AlgRAM
import Definitions.Def_RSCapacity_ListRecovery
import Definitions.Def_RSCapacity_DecoderIO

open Polynomial

set_option autoImplicit false

namespace RSCapacity

/-- **Theorem 1.1 (Capacity decoding and field-size-independent lists).** Jeronimo,
arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Theorem 1.1, pp.1–2
(PDF 3–4). Fix γ ∈ (0, 1) and an integer L ≥ 1. There are effective constants
C_alg = C_alg(γ, L), C_list = C_list(γ, L), and n_0 = n_0(γ, L) such that the following holds. Let
n ≥ n_0, let q ≥ n be prime, let D ⊆ 𝔽_q have n distinct points, and let 1 ≤ k ≤ (1 − γ)n. For
arbitrary lists |S_i| ≤ L, all polynomials in ℒ(D, k, 𝐒, k + ⌈γn⌉) can be found deterministically
using at most q^{C_alg} field operations. Moreover, |ℒ(D, k, 𝐒, k + ⌈γn⌉)| ≤ n^{C_list}. In
particular, every such Reed–Solomon code is list decodable at radius 1 − k/n − γ, with polynomial
list size independent of q and deterministic polynomial time whenever q = n^{O(1)}.

**Formalization Note.**
* (a) "Found deterministically using at most q^{C_alg} field operations": one coin-free program of
  the published algebraic RAM `MatroidSensOracle.aexec` over `ZMod q`, chosen with the constants
  after γ, L and before n, q, D, k, 𝐒. It halts within q^{C_alg} steps (word steps are counted too)
  for every word length w with q^{C_alg} < 2^w, and outputs every polynomial of ℒ exactly once and
  nothing else. Input: words `[n, k, A, |S_1|, …, |S_n|]` with A = k + ⌈γn⌉, field cells
  `[α_1, …, α_n] ++ S_1 ++ ⋯ ++ S_n`, each S_i a duplicate-free list in any order (empty lists
  allowed).
* (b) |ℒ| is `Set.encard`, so finiteness is part of the claim.
* (c) The radius statement: every Hamming ball of relative radius 1 − k/n − γ contains at most
  n^{C_list} codewords of RS_{𝔽_q}(D, k). Its "deterministic polynomial time whenever q = n^{O(1)}"
  is (a) at singleton lists (q ≤ n^c gives q^{C_alg} ≤ n^{c·C_alg}).
* "Effective" describes how the constants arise; it is not a formal clause. -/
theorem theorem_1_1_capacity_list_recovery (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (L : ℕ)
    (hL : 1 ≤ L) :
    ∃ (Calg Clist n₀ : ℕ) (prog : List MatroidSensOracle.AInstr),
      (∀ ins ∈ prog, ¬ ins.IsCoin) ∧
      ∀ (n q : ℕ) [Fact q.Prime], n₀ ≤ n → n ≤ q →
      ∀ α : Fin n → ZMod q, Function.Injective α →
      ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ (1 - γ) * n →
      ∀ S : Fin n → List (ZMod q), (∀ i, (S i).Nodup) → (∀ i, (S i).length ≤ L) →
        (∀ w : ℕ, q ^ Calg < 2 ^ w →
          ∃ st, MatroidSensOracle.aexec prog (fun _ => 0) (q ^ Calg) 0 0
              (MatroidSensOracle.aloadWords w (listInstanceWords k (k + ⌈γ * n⌉₊) S))
              (MatroidSensOracle.aloadFields (listInstanceFields α S)) = some st ∧
            OutputsExactly k st (listSet α k (fun i => (S i).toFinset) (k + ⌈γ * n⌉₊))) ∧
        (listSet α k (fun i => (S i).toFinset) (k + ⌈γ * n⌉₊)).encard ≤ ((n ^ Clist : ℕ) : ℕ∞) ∧
        ∀ y : Fin n → ZMod q,
          {c | c ∈ rsCode α k ∧ (hammingDist y c : ℝ) / n ≤ 1 - (k : ℝ) / n - γ}.encard ≤
            ((n ^ Clist : ℕ) : ℕ∞) := by sorry

end RSCapacity
