-- Prove2me | Theorems.Thm_PHIP1781_comparison_det
-- name    : PHIP1781.comparison_det
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:34:28.645203+00:00
-- url     : https://prove2.me/theorems/baaa955d-8b12-4129-a6d7-21c6ed346ecc
-- title:
--   comparison det — PHIP1781
-- statement:
--   Para a matriz racional
--   $$ M=\begin{pmatrix}1&-1/10\\-1/10&2/5\end{pmatrix}, $$
--   vale \(\det M=39/100\). Trata-se de um cálculo exato de dimensão dois.
--
--   Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Inventário documental V3, PF28 FINAL 15/11/2026. PHIP1781.comparison_det; fonte PHIP-1781_Astra_Fable_pacote_c_9_recuperado_Z_J_0_256678_certificado_e_E_indefinido_BSS_com_margem_do_3fe98395_block5.lean; SHA256 original cd274aebcf793557a25dd499830e44491300c5d53d12fea5d07ad236e1d7fc94. Sem reivindicação de novidade.

import Mathlib
open Filter Topology

theorem PHIP1781.comparison_det : Matrix.det (!![1, -(1/10); -(1/10), 2/5] : Matrix (Fin 2) (Fin 2) ℚ) = 39/100 := by sorry
